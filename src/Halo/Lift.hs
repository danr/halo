{-

    Lift inner case-expressions and let-expressions to the top level.

    If there are remaining lambdas from the GHC lambda lifter, we lift
    these as well.

-}
module Halo.Lift ( caseLetLift, LiftSettings(..) ) where

import CoreFVs
import CoreUtils
import CoreSyn
import Id
import Name
import MkCore
import OccName
import Type
import UniqSupply
import Unique
import Var
import VarSet

import Halo.Util
import Halo.Shared

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Applicative

data LiftSettings = LiftSettings
    { lift_inner  :: Bool
    , lift_to_ueq :: Bool
    }

-- | The lift environment, current function and its arguments
data LiftEnv = LiftEnv
    { fun      :: Var
    , args     :: [Var]
    , settings :: LiftSettings
    }

modArgs :: ([Var] -> [Var]) -> LiftEnv -> LiftEnv
modArgs k env = env { args = k (args env) }

setFun :: Var -> LiftEnv -> LiftEnv
setFun f env = env { fun = f }

-- | The initial environment
initEnv :: LiftSettings -> LiftEnv
initEnv = LiftEnv (error "initEnv: fun") []

-- | The lift monad
type LiftM = WriterT [CoreBind] (ReaderT LiftEnv (WriterT [String] UniqSM))

-- | Write a debug message
dbgMsg :: String -> LiftM ()
dbgMsg = lift . tell . return

-- | Get a new unique identifier from the UniqSM
liftUnique :: LiftM Unique
liftUnique = lift . lift . lift $ getUniqueM

run :: LiftM a -> LiftSettings -> UniqSupply -> (((a,[CoreBind]),[String]),UniqSupply)
run m s us = initUs us (runWriterT (runWriterT m `runReaderT` initEnv s))

-- | caseLetLift a core program
caseLetLift :: [CoreBind] -> LiftSettings -> UniqSupply -> (([CoreBind],[String]),UniqSupply)
caseLetLift []     _ us = (([],[]),us)
caseLetLift (b:bs) s us =
    ((mkCoreBind (flattenBinds (b':lifted_binds)):more_binds
     ,msgs++more_msgs)
    ,fin_us)
   where
     (((b',lifted_binds),msgs),us')  = run (liftCoreBind b) s us
     ((more_binds,more_msgs),fin_us) = caseLetLift bs s us'

-- | Lift a binding group
liftCoreBind :: CoreBind -> LiftM CoreBind
liftCoreBind b = case b of
    NonRec f e -> NonRec f <$> liftDecl f e
    Rec binds  -> Rec <$> sequence [ (,) f <$> liftDecl f e | (f,e) <- binds ]

-- | Translate a CoreDecl or a Let
liftDecl :: Var -> CoreExpr -> LiftM CoreExpr
liftDecl f e = do
    dbgMsg $ "Lifting " ++ idToStr f ++ ", args: " ++ unwords (map idToStr as)
    dbgMsg $ "    rhs:" ++ showExpr e
    args_ <- asks args
    e_lifted <- local (setFun f . modArgs (++as)) (liftCase e_stripped)
    return (mkCoreLams (args_ ++ as) e_lifted)
  where
    (as,e_stripped) = collectBinders e

isVar :: CoreExpr -> Bool
isVar e0 = case e0 of
    Var{} -> True
    Cast e _ -> isVar e
    _ -> False

-- | Translate a case expression
liftCase :: CoreExpr -> LiftM CoreExpr
liftCase e = do
    ueq <- asks (lift_to_ueq . settings)
    case e of
        Case scrutinee scrut_var ty alts

            | ueq && not (isVar scrutinee) -> do
                dbgMsg $ "UEQ and not a var scrutinee: " ++ showOutputable e
                liftInnerCase scrutinee scrut_var ty alts

            | otherwise -> do

                dbgMsg $ "Case on " ++ showExpr scrutinee

                lifted_scrutinee <- liftExpr scrutinee

                lifted_alts <- mapM liftAlt alts

                return $ Case lifted_scrutinee scrut_var ty lifted_alts

        _ -> liftExpr e

-- | Lift an alternative
liftAlt :: CoreAlt -> LiftM CoreAlt
liftAlt (con,bound,e) = do
    li <- asks (lift_inner . settings)
    let liftInner = if li then liftExpr else liftCase
    e_lifted <- local (modArgs (++ bound)) (liftInner e)
    return (con,bound,e_lifted)

-- | Lift an expression
liftExpr :: CoreExpr -> LiftM CoreExpr
liftExpr e = case e of
    Var _          -> return e
    Lit _          -> return e
    Type _         -> return e
    Coercion _     -> return e

    Lam y e'       -> liftInnerLambda y e'
    Let bind in_e  -> liftInnerLet bind in_e
    Case s sv t as -> liftInnerCase s sv t as

    App e1 e2      -> App <$> liftExpr e1 <*> liftExpr e2
    Cast e_cast c  -> Cast <$> liftExpr e_cast <*> pure c
    Tick t e_tick  -> Tick t <$> liftExpr e_tick

-- | Make a new name for something that is lifted out, by attaching a label
--   to the current function
mkLiftedName :: Type -> String -> LiftM Var
mkLiftedName ty lbl = do
    i <- liftUnique
    fun_var <- asks fun
    let fun_desc = idToStr fun_var
        name = mkSystemName i (mkOccName OccName.varName (fun_desc ++ "_" ++ lbl))
        var' = mkLocalId name ty
    return var'

-- | Lift inner lambda expression
liftInnerLambda :: Var -> CoreExpr -> LiftM CoreExpr
liftInnerLambda x e = do

    let fv_set = exprFreeVars e

    lam_args <- filter (`elemVarSet` fv_set) <$> asks args

    let lam_args_x = lam_args ++ [x]

    new_fun <- mkLiftedName (mkPiTypes lam_args_x (exprType e)) "lam"

    dbgMsg $ "Lift lambda: " ++ showExpr (Lam x e) ++ " new name: " ++ showOutputable new_fun

    lifted_lam <- local (modArgs (const lam_args_x) . setFun new_fun)
                        (liftCoreBind (NonRec new_fun e))

    tell [lifted_lam]

    return $ mkVarApps (Var new_fun) lam_args

-- | Lift an inner case expression
liftInnerCase :: CoreExpr -> Var -> Type -> [CoreAlt] -> LiftM CoreExpr
liftInnerCase scrutinee scrut_var ty alts = do

    -- lift cases out of the scrutinee
    scrutinee' <- liftExpr scrutinee

    dbgMsg $ "liftInnerCase: lifted " ++ showExpr scrutinee ++ " to " ++ showExpr scrutinee'

    new_var <- mkLiftedName ty "case_var"

    dbgMsg $ "liftInnerCase: new variable: " ++ showOutputable new_var

    let e = Case (Var new_var) scrut_var ty alts

    dbgMsg $ "liftInnerCase: new case: " ++ showOutputable e

    arg_vars <- asks args

    let fv_set    = exprFreeVars (Case scrutinee scrut_var ty alts)
        case_args = filter (`elemVarSet` fv_set) arg_vars

    dbgMsg $ "liftInnerCase: case args: " ++ showOutputable case_args

    new_fun <- mkLiftedName (mkPiTypes (new_var:case_args) ty) "case"

    dbgMsg $ "liftInnerCase: new fun: " ++ showOutputable new_fun

    lifted_case <- local (modArgs (const (new_var:case_args)) . setFun new_fun)
                         (liftCoreBind (NonRec new_fun e))
    tell [lifted_case]

    dbgMsg $ "liftInnerCase: lifted case: " ++ showOutputable lifted_case

    let ret = mkApps (Var new_fun) (scrutinee':map Var case_args)

    dbgMsg $ "liftInnerCase: returning: " ++ showOutputable ret

    return ret

-- | Lift a let expression
liftInnerLet :: CoreBind -> CoreExpr -> LiftM CoreExpr
liftInnerLet b in_e = do
    dbgMsg $ "Experimental let: " ++ showExpr (Let b in_e)
    case b of
        NonRec v e -> do
            (lifted_bind,subst_pair) <- liftInnerDecl v e

            tell [uncurry NonRec lifted_bind]

            liftExpr (substExprList [subst_pair] in_e)

        Rec binds -> do
            (lifted_binds,subst_list) <- mapAndUnzipM (uncurry liftInnerDecl) binds

            tell [Rec lifted_binds]

            liftExpr (substExprList subst_list in_e)

-- | Returns the substitution
liftInnerDecl :: Var -> CoreExpr -> LiftM ((Var,CoreExpr),(Var,CoreExpr))
liftInnerDecl v e = do

    arg_vars <- asks args

    let fv_set   = bindFreeVars (NonRec v e)
        let_args = filter (`elemVarSet` fv_set) arg_vars

    new_v <- mkLiftedName (mkPiTypes arg_vars (varType v))
                          (idToStr v ++ "let")

    let subst_v = mkVarApps (Var new_v) let_args

    lifted_e <- local (modArgs (const let_args))
                      (liftDecl new_v (substExp v subst_v e))

    return ((new_v,lifted_e),(v,subst_v))
