-- Linearises (pretty prints) our UEQ FOL
-- representation into Waldmeister format
module Halo.FOL.LineariseWaldmeister (linWaldmeister) where

import Outputable hiding (quote)

import Data.List
import Data.Ord

import Halo.Shared
import Halo.Util
import Halo.FOL.Internals.Internals
import Halo.FOL.Operations
import Halo.FOL.Abstract

import Data.Generics.Geniplate
import qualified Data.Set as S
import Data.Set (Set)
import Data.Maybe

-- | Linearise a set of clauses to a String
linWaldmeister :: [StrClause] -> String
linWaldmeister = (++ "\n") . portableShowSDoc . linClauses

-- | Linearise the set of clauses, producing unsat cores if the Bool is true
linClauses :: [StrClause] -> SDoc
linClauses cls = vcat
    [ text "NAME" <+> text "hipspec"
    , text "MODE" <+> text "PROOF"
    , text "SORTS" <+> linDomain

    , hang (text "SIGNATURE") 4 (vcat sigs)

    , hang (text "ORDERING") 4 (vcat
            [text "LPO",cat (punctuate (text ">") order)]
        )

    , hang (text "VARIABLES") 4
        (cat (punctuate comma vars) <+> colon <+> linDomain)

    , hang (text "EQUATIONS") 4 (vcat eqs)
    , hang (text "CONCLUSION") 4 concl
    ]
  where
    (pos_eqs,neg_eq:_)
        = map fst *** map fst
        $ partition snd
        $ mapMaybe clauseToEq cls

    order :: [SDoc]
    order = map text
          $ (any appUsed cls ? ("app":))
          $ map fst
          $ sortBy (flip $ comparing snd)
          $ symbols

    symbols :: [(String,Int)]
    symbols = S.toList . S.unions . map get . universeBi $ cls
      where
        get :: StrTerm -> Set (String,Int)
        get (Fun v as)   = S.singleton (v,length as)
        get (Ctor v as)  = S.singleton (v,length as)
        get (Skolem v)   = S.singleton (v,0)
        get (Ptr v)      = S.singleton (v,0)
        get _            = S.empty

    sigs :: [SDoc]
    sigs = [ text s
                <+> colon
                <+> cat (punctuate space (replicate a linDomain))
                <+> arrow
                <+> linDomain
           | (s,a) <- symbols
           ]

    vars :: [SDoc]
    vars = map text $ nub $ concatMap allQuant' cls

    concl :: SDoc
    eqs :: [SDoc]
    concl:eqs = map (uncurry linEquality) (neg_eq:pos_eqs)

clauseToEq :: StrClause -> Maybe ((StrTerm,StrTerm),Bool)
clauseToEq cl = case cl of
    Comment{} -> Nothing
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
linTerm tm = case tm of
    Fun s []    -> text s
    Fun s tms   -> text s <+> linTerms tms
    Ctor s []   -> text s
    Ctor s tms  -> text s <+> linTerms tms
    Skolem s    -> text s
    App t1 t2   -> linApp <+> linTerms [t1,t2]
    Ptr a       -> text a
    QVar a      -> text a
    Prim{}      -> error "Waldmeister prim"
    Lit{}       -> error "Waldmeister lit"
    Proj{}      -> error "Waldmeister proj"
  where
    linTerms = parens . cat . punctuate comma . map linTerm

-- | Our domain D
linDomain :: SDoc
linDomain = char 'D'

-- | The app/@ symbol
linApp      :: SDoc
linApp      = text "app"

