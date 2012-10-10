{-# LANGUAGE ScopedTypeVariables #-}
module Halo.FOL.Operations where

import Halo.FOL.Internals.Internals

import Data.Generics.Geniplate

import qualified Data.Set as S
import Data.Set (Set)

replaceVarsTm :: (v -> u)
              -> Term q v -> Term q u
replaceVarsTm k = go
  where
    go tm = case tm of
        Fun v as   -> Fun (k v) (map go as)
        Ctor v as  -> Ctor (k v) (map go as)
        Skolem v   -> Skolem (k v)
        App t1 t2  -> App (go t1) (go t2)
        Proj i v a -> Proj i (k v) (go a)
        Ptr v      -> Ptr (k v)
        QVar q     -> QVar q
        Prim p as  -> Prim p (map go as)
        Lit i      -> Lit i

replaceQVarsTm :: (q -> r)
               -> Term q v -> Term r v
replaceQVarsTm k = go
  where
    go tm = case tm of
        Fun v as   -> Fun v (map go as)
        Ctor v as  -> Ctor v (map go as)
        Skolem v   -> Skolem v
        App t1 t2  -> App (go t1) (go t2)
        Proj i v a -> Proj i v (go a)
        Ptr v      -> Ptr v
        QVar q     -> QVar (k q)
        Prim p as  -> Prim p (map go as)
        Lit i      -> Lit i

formulaMapTerms :: (Term q v -> Term r u)
                -> (q -> r)
                -> Formula q v -> Formula r u
formulaMapTerms tm qv = go
  where
    go f = case f of
        Equal t1 t2   -> Equal (tm t1) (tm t2)
        Unequal t1 t2 -> Unequal (tm t1) (tm t2)
        And fs        -> And (map go fs)
        Or fs         -> Or (map go fs)
        Implies f1 f2 -> Implies (go f1) (go f2)
        Neg f'        -> Neg (go f')
        Forall qs f'  -> Forall (map qv qs) (go f')
        Exists qs f'  -> Exists (map qv qs) (go f')
        Pred p ts     -> Pred p (map tm ts)

clauseMapTerms :: (Term q v -> Term r u) -> (q -> r)
               -> Clause q v -> Clause r u
clauseMapTerms tm qv cl = case cl of
    Clause c s f -> Clause c s (formulaMapTerms tm qv f)
    Comment s    -> Comment s

clauseMapFormula :: (Formula q v -> Formula r u)
                 -> Clause q v -> Clause r u
clauseMapFormula k cl = case cl of
    Clause c s f -> Clause c s (k f)
    Comment s    -> Comment s

allSymbolsOfTerms :: Ord v => [Term q v] -> S.Set v
allSymbolsOfTerms tms = S.unions (map allSymbolsOfTerm tms)

allSymbolsOfTerm :: Ord v => Term q v -> S.Set v
allSymbolsOfTerm x
  = go x S.empty
  where go (Fun v tms) acc   = foldr go (v `S.insert` acc) tms
        go (Ctor v tms) acc  = foldr go (v `S.insert` acc) tms
        go (Skolem v) acc    = v `S.insert` acc
        go (Proj _ v tm) acc = go tm (v `S.insert` acc)
        go (Ptr v) acc       = v `S.insert` acc
        go (QVar _) acc      = acc
        go (Prim _ tms) acc  = foldr go acc tms
        go (Lit _) acc       = acc
        go (App t1 t2) acc   = foldr go acc [t1,t2]

allSymbolsOfForm :: Ord v => Formula q v -> S.Set v
allSymbolsOfForm x
  = go x S.empty
  where go (Equal t1 t2) acc   = S.union (allSymbolsOfTerms [t1,t2]) acc
        go (Unequal t1 t2) acc = S.union (allSymbolsOfTerms [t1,t2]) acc
        go (And fms) acc = foldr go acc fms
        go (Or fms) acc  = foldr go acc fms
        go (Implies f1 f2) acc = foldr go acc [f1,f2]
        go (Forall _ fm) acc = go fm acc
        go (Exists _ fm) acc = go fm acc
        go (Pred _ tms) acc  = S.union (allSymbolsOfTerms tms) acc
        go (Neg fm) acc      = go fm acc
        
allSymbolsOfClause :: Ord v => Clause q v -> S.Set v
allSymbolsOfClause (Clause _ _ fm) = allSymbolsOfForm fm
allSymbolsOfClause _ = S.empty


allQuantOfTerms :: Ord q => [Term q v] -> S.Set q
allQuantOfTerms tms = S.unions (map allQuantOfTerm tms)

allQuantOfTerm :: Ord q => Term q v -> S.Set q
allQuantOfTerm x
  = go x S.empty
  where go (Fun _v tms) acc   = foldr go acc tms
        go (Ctor _v tms) acc  = foldr go acc tms
        go (Skolem _v) acc    = acc
        go (Proj _ _v tm) acc = go tm acc
        go (Ptr _v) acc       = acc
        go (QVar q) acc       = q `S.insert` acc
        go (Prim _ tms) acc   = foldr go acc tms
        go (Lit _) acc        = acc
        go (App t1 t2) acc    = foldr go acc [t1,t2]

allQuantOfForm :: Ord q => Formula q v -> S.Set q
allQuantOfForm x
  = go x S.empty
  where go (Equal t1 t2) acc   = S.union (allQuantOfTerms [t1,t2]) acc
        go (Unequal t1 t2) acc = S.union (allQuantOfTerms [t1,t2]) acc
        go (And fms) acc = foldr go acc fms
        go (Or fms) acc  = foldr go acc fms
        go (Implies f1 f2) acc = foldr go acc [f1,f2]
        go (Forall qs fm) acc  = go fm (S.fromList qs `S.union` acc) -- Is this right?
        go (Exists qs fm) acc  = go fm (S.fromList qs `S.union` acc) -- Is this right? 
        go (Pred _ tms) acc    = S.union (allQuantOfTerms tms) acc
        go (Neg fm) acc        = go fm acc

-- allQuant :: forall q v . Ord q => Formula q v -> [q]
-- allQuant phi = S.toList . S.unions $
--     map getTm (universeBi phi) ++ map getFm (universeBi phi)
--   where
--     getTm :: Term q v -> Set q
--     getTm (QVar v) = S.singleton v
--     getTm _        = S.empty

--     getFm :: Formula q v -> Set q
--     getFm (Forall qs _) = S.fromList qs
--     getFm _             = S.empty

allQuantOfClause :: Ord q => Clause q v -> S.Set q
allQuantOfClause (Clause _ _ f) = allQuantOfForm f
allQuantOfClause (Comment _ )   = S.empty


substVar :: Eq v => v -> v -> Formula q v -> Formula q v
substVar old new
  = formulaMapTerms (replaceVarsTm subst_var) id
  where subst_var x = if x == old then new else x
 
-- substQVarX :: Eq q => q -> q -> Formula q v -> Formula q v
-- -- Rewrites the qvars in a quantifier-free formula 
-- substQVarX old new 
--  = formulaMapTerms rewrite_qvar id
--  where rewrite_qvar (QVar v) | v == old = QVar new
--        rewrite_qvar other               = other

{- 
substVars :: forall q v . Eq v => v -> v -> Formula q v -> Formula q v
substVars old new = rewriteBi s
  where
    s :: Term q v -> Maybe (Term q v)
    s (Fun v as)   | v == old = Just (Fun new as)
    s (Ctor v as)  | v == old = Just (Ctor new as)
    s (Proj i v a) | v == old = Just (Proj i new a)
    s (Ptr v)      | v == old = Just (Ptr new)
    s _                       = Nothing

substQVar :: forall q v . Eq q => q -> q -> Formula q v -> Formula q v
substQVar old new = rewriteBi s
  where
    s :: Term q v -> Maybe (Term q v)
    s (QVar v) | v == old = Just (QVar new)
    s _                   = Nothing

rewriteBi :: forall s t . (TransformBi s s,TransformBi s t) => (s -> Maybe s) -> t -> t
rewriteBi f = transformBi g
  where
    g :: s -> s
    g x = maybe x (rewriteBi f) (f x)
-}

-- Querying

funsUsed :: forall q v . Ord v => Clause q v -> Set (v,Int)
funsUsed cl    = S.fromList [ (f,length as) | Fun f as :: Term q v <- universeBi cl ]

consUsed :: forall q v . Ord v => Clause q v -> Set (v,Int)
consUsed cl    = S.fromList [ (c,length as) | Ctor c as :: Term q v <- universeBi cl ]

ptrsUsed :: forall q v . Ord v => Clause q v -> Set v
ptrsUsed cl    = S.fromList [ p | Ptr p :: Term q v <- universeBi cl ]

primsUsed :: forall q v . Ord v => Clause q v -> Set Prim
primsUsed cl   = S.fromList [ p | Prim p _ :: Term q v <- universeBi cl ]

skolemsUsed :: forall q v . Ord v => Clause q v -> Set v
skolemsUsed cl = S.fromList [ s | Skolem s :: Term q v <- universeBi cl ]

appUsed :: forall q v . Ord v => Clause q v -> Bool
appUsed cl     = or [ True | App{}  :: Term q v <- universeBi cl ]

predUsed :: forall q v . Ord v => Pred -> Clause q v -> Bool
predUsed p cl = or  [ p == p' | Pred p' _ :: Formula q v <- universeBi cl ]

minUsed :: Ord v => Clause q v -> Bool
minUsed = predUsed Min

minRecUsed :: Ord v => Clause q v -> Bool
minRecUsed = predUsed MinRec

cfUsed :: Ord v => Clause q v -> Bool
cfUsed = predUsed CF
