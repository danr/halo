-- Linearises (pretty prints) our UEQ FOL
-- representation into Waldmeister format
module Halo.FOL.LineariseWaldmeister (linWaldmeister) where

import Outputable hiding (quote)

import Data.List
import Control.Arrow ((***))

import Var
import TysPrim
import Type
import TysWiredIn
import DataCon

import Halo.Shared
import Halo.Util
import Halo.FOL.Internals.Internals
import Halo.FOL.Operations
import Halo.FOL.Abstract

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe

-- | Linearise a set of clauses to a String
linWaldmeister :: [StrClause] -> String
linWaldmeister = (++ "\n") . portableShowSDoc . linClauses

-- | Linearise the set of clauses, producing unsat cores if the Bool is true
linClauses :: [StrClause] -> SDoc
linClauses cls = vcat $ concat
    [ text "NAME" <+> text "hipspec"
    , text "MODE" <+> text "PROOF"
    , text "SORTS" <+> linDomain

    , hang (text "SIGNATURE") 4 (vcat sigs)

    , hang (text "ORDERING") 4 (vcat (text "LPO":order)

    , hang (text "VARIABLES") 4
        (punctuate comma vars <+> colon <+> linDomain)

    , hang (text "EQUATIONS") 4 (vcat eqs)
    , hang (text "CONCLUSION") 4 (vcat concls)
    ]
  where
    (pos_eqs,neg_eqs)
        = map fst *** map fst
        $ partition snd
        $ mapMaybe clasueToEqs cls

    symbols = S.toList . S.unions . map get . universeBi
      where
        get :: Term' -> Set SDoc
        get (Fun v _)    = S.singleton v
        get (Ctor v _)   = S.singleton v
        get (Skolem v)   = S.singleton v
        get (Proj _ v _) = S.singleton v
        get (Ptr v)      = S.singleton v
        get _            = S.empty



clauseToEq :: Clause' -> Maybe ((StrTerm,StrTerm),Bool)
clauseToEq cl = case cl of
    Comment s -> Nothing
    Clause _ cl_type cl_formula -> do
        let cl_formula' = (cl_type == Conjecture ? neg) cl_formula
        [lit] <- simpleCNF cl_formula'
        case lit of
            Equal t1 t2   -> Just ((t1,t2),True)
            Unequal t1 t2 -> Just ((t1,t2),False)
            _             -> Nothing

linEquality :: StrTerm -> StrTerm -> SDoc
linEquality t1 t2 = linTerm t1 <+> equals <+> linTerm t2

-- | Linearise a term
--   The way to carry out most of the work is determined in the Style.
linTerm :: StrTerm -> SDoc
linTerm (Skolem a) = linSkolem a
linTerm tm = case tm of
    Fun s []    -> text s
    Fun s tms   -> parens $ text s <+> linTerms tms
    Ctor s []   -> text s
    Ctor s tms  -> parens $ text s <+> linTerms tms
    Skolem s    -> text s
    App t1 t2   -> parens $ linApp <+> linTerms [t1,t2]
    Ptr a       -> text a
    QVar a      -> text a
    Prim{}      -> error "Waldmeister prim"
    Lit{}       -> error "Waldmeister lit"
    Proj{}      -> error "Waldmeister proj"
  where
    linTerms = punctuate comma . map linTerm

-- | Our domain D
linDomain :: SDoc
linDomain = char 'D'

-- | Short representation of a Var to String
showVar :: Var -> String
showVar v = (++ "_" ++ show (varUnique v)) . escape . idToStr $ v

-- | Pretty printing functions and variables
linFun      :: Var -> SDoc
linFun      = text . ("f_" ++) . showVar

-- | Pretty printing constructors
linCtor     :: Var -> SDoc
linCtor     = text . ("c_" ++) . showVar

-- | Pretty printing Skolemised variables
linSkolem   :: Var -> SDoc
linSkolem   = text . ("a_" ++) . showVar

-- | Quantified variables
linQuantVar :: Var -> SDoc
linQuantVar = text . ("q_" ++) . showVar

-- | The app/@ symbol
linApp      :: SDoc
linApp      = text "app"

-- | Pointers
linPtr      :: Var -> SDoc
linPtr      = text . ("p_" ++) . showVar

-- | Escaping
escape :: String -> String
escape = concatMap (\c -> fromMaybe [c] (M.lookup c escapes))

-- | Some kind of z-encoding escaping
escapes :: Map Char String
escapes = M.fromList $ map (uncurry (flip (,)))
    [ ("za",'@')
    , ("z_",'\'')
    , ("z1",'(')
    , ("z2",')')
    , ("zb",'!')
    , ("zB",'}')
    , ("zc",':')
    , ("zC",'%')
    , ("zd",'$')
    , ("ze",=')
    , ("zG",'>')
    , ("zh",'-')
    , ("zH",'#')
    , ("zi",'|')
    , ("zl",']')
    , ("zL",'<')
    , ("zm",',')
    , ("zn",'&')
    , ("zo",'.')
    , ("zp",'+')
    , ("zq",'?')
    , ("zr",'[')
    , ("zR",'{')
    , ("zs",'*')
    , ("zS",' ')
    , ("zt",'~')
    , ("zT",'^')
    , ("zv",'/')
    , ("zV",'\\')
    , ("zz",'z')
    ]

