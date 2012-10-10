{-# LANGUAGE PatternGuards, FlexibleContexts #-}
-- (c) Dan Rosén 2012
module Halo.FOL.Abstract
    ( VTerm, VFormula, VClause
    , STerm, SFormula, SClause

    -- , apply, con

    -- , fun, fun0
    -- , ctor, ctor0

    , conApp, funApp, funOrConApp
    , app, apps
    , proj
    , qvar
    , skolem
    , ptr
    , prim
    , litInteger

    , isAtomic
    , simpleCNF
    , splitFormula, splitFormulae

      -- Logical connectives and formula introductions
    , (===), (=/=)
    , (==>), (===>)
    , (<=>), (<==>)
    , (/\), ands
    , (\/), ors
    , neg
    , qforall, qexists
    , qforalls

      -- Predicates 
    , minPred
    , minRecPred
    , cfPred, ecfPred
    , isTypePred
    , evalPred
      
    , Formula
    , Term
    , Prim(..)
    , ClType
    , Clause
    , clause
    , comment
    , namedClause
    , clauseSplit

    , axiom, lemma, hypothesis, definition
    , conjecture, negatedConjecture, question

    , axioms, definitions
    ) where

import Var
import Id

import Halo.FOL.Internals.Internals
import Halo.FOL.Operations

import Halo.FreeTyCons (isNewtypeConId)

import qualified Data.Set as Set

-- Terms with variables 
type VTerm    = Term    Var Var
type VFormula = Formula Var Var
type VClause  = Clause  Var Var

type STerm    = Term    String String
type SFormula = Formula String String
type SClause  = Clause  String String

comment :: String -> Clause q v
comment = Comment

clause :: ClType -> Formula q v -> Clause q v
clause = Clause "x"

namedClause :: String -> ClType -> Formula q v -> Clause q v
namedClause = Clause

clauseSplit :: ClType -> Formula q v -> [Clause q v]
clauseSplit cl_type = map (clause cl_type) . splitFormula


-- | Figure out if this var is one of the primitive constants, or if
--   it is a data constructor or a function, and make a term accordingly.
funOrConApp :: Var -> [Term q Var] -> Term q Var
funOrConApp x as
    | isId x && (isConLikeId x || isNewtypeConId x) = Ctor x as
    | otherwise                                     = funApp x as

-- -- | Make a term of this primitive constant, constructor or CAF.
-- con :: Var -> Term q Var
-- con x = apply x []

-- fun :: v -> [Term q v] -> Term q v
-- fun = Fun

-- fun0 :: v -> Term q v
-- fun0 a = Fun a []

-- ctor :: v -> [Term q v] -> Term q v
-- ctor = Ctor

-- ctor0 :: v -> Term q v
-- ctor0 a = Ctor a []

conApp :: Var -> [Term q Var] -> Term q Var
-- Precondition: isId x && (isConLikeId x || isNewtypeConId x)
conApp = Ctor

funApp :: Var -> [Term q Var] -> Term q Var
-- Precondition: is variable
funApp v = Fun v -- foldl App (Ptr v)

app :: Term q Var -> Term q Var -> Term q Var
app = App 

apps :: Term q Var -> [Term q Var] -> Term q Var
apps = foldl App

proj :: Int -> v -> Term q v -> Term q v
proj = Proj

qvar :: q -> Term q v
qvar = QVar

skolem :: v -> Term q v
skolem = Skolem

ptr :: v -> Term q v
ptr = Ptr

prim :: Prim -> [Term q v] -> Term q v
prim = Prim

litInteger :: Integer -> Term q v
litInteger = Lit

infix 4 ===
infix 4 =/=

(===),(=/=) :: Term q v -> Term q v -> Formula q v
(===) = Equal
(=/=) = Unequal

infixl 1 ==>, ===>

infix 1 <=>, <==>

-- | Implication
(==>) :: Formula q v -> Formula q v -> Formula q v
(==>) = Implies

-- | [l1,..,ln] ===> r means
--   l1 /\ .. /\ ln ==> r1
(===>) :: [Formula q v] -> Formula q v -> Formula q v
[]  ===> f = f
phi ===> f = ands phi ==> f

-- | Equivalence
(<=>) :: Formula q v -> Formula q v -> Formula q v
x <=> y = (x ==> y) /\ (y ==> x)

-- | l <==> [r1,..,r2] means
--   l <==> r1 /\ ... /\ r2
(<==>) :: Formula q v -> [Formula q v] -> Formula q v
x <==> [] = x
x <==> ys = (x ==> ands ys) /\ (ands ys ==> x)

infixr 2 \/
infixr 3 /\

(\/),(/\) :: Formula q v -> Formula q v -> Formula q v
a \/ b = ors [a,b]
a /\ b = ands [a,b]

ands :: [Formula q v] -> Formula q v
ands []  = error "ands: Empty list"
ands [f] = f
ands fs  = And (concatMap flattenAnd fs)

flattenAnd :: Formula q v -> [Formula q v]
flattenAnd (And fs) = concatMap flattenAnd fs
flattenAnd f        = [f]

ors :: [Formula q v] -> Formula q v
ors []  = error "ors: Empty list"
ors [f] = f
ors fs  = Or (concatMap flattenOr fs)

flattenOr :: Formula q v -> [Formula q v]
flattenOr (Or fs) = concatMap flattenOr fs
flattenOr f       = [f]

neg :: Formula q v -> Formula q v
neg (Neg f)         = f
neg (Equal t1 t2)   = Unequal t1 t2
neg (Unequal t1 t2) = Equal t1 t2
neg (And fs)        = Or (map neg fs)
neg (Or fs)         = And (map neg fs)
neg (Implies f1 f2) = neg f2 `Implies` neg f1
neg (Forall as f)   = Exists as (neg f)
neg (Exists as f)   = Forall as (neg f)
neg f               = Neg f

qforall :: [q] -> Formula q v -> Formula q v
qforall [] f = f
qforall as f = Forall as f

qexists :: [q] -> Formula q v -> Formula q v
qexists [] f = f
qexists as f = Exists as f

qforalls :: Ord q => Formula q v -> Formula q v
qforalls fm = qforall qvars fm
  where qvars = Set.toList (allQuantOfForm fm)
        

minPred :: Term q v -> Formula q v
minPred t = Pred Min [t]

minRecPred :: Term q v -> Formula q v
minRecPred t = Pred MinRec [t]

cfPred :: Term q v -> Formula q v
cfPred t = Pred CF [t]

ecfPred :: Term q v -> Formula q v
ecfPred t = Pred ECF [t]

isTypePred :: Term q v -> Term q v -> Formula q v
isTypePred t1 t2 = Pred IsType [t1,t2]

evalPred :: Term q v -> Term q v -> Formula q v
evalPred t1 t2 = Pred Eval [t1,t2]

type Atomic q v = Formula q v

isAtomic :: Formula q v -> Bool
isAtomic f = case f of
    Equal{}     -> True
    Unequal{}   -> True
    Or{}        -> False
    And{}       -> False
    Implies{}   -> False
    (Neg Neg{}) -> False
    (Neg x)     -> isAtomic x
    Forall{}    -> False
    Exists{}    -> False
    Pred{}      -> True

-- | Can this formula be written simply in CNF?
simpleCNF :: Formula q v -> Maybe [Atomic q v]
simpleCNF (Forall _ _f)             = Nothing 
simpleCNF (Implies f1 f2)           = simpleCNF (neg f1 \/ f2)
simpleCNF (Or fs) | all isAtomic fs = Just fs
simpleCNF f       | isAtomic f      = Just [f]
simpleCNF _                         = Nothing

-- | Split the conjuncts of a formula over many formulae,
--   distributing any foralls over them
splitFormula :: Formula q v -> [Formula q v]
splitFormula (Forall vs fs) = map (qforall vs) (splitFormula fs)
splitFormula (And fs)       = concatMap splitFormula fs
splitFormula f              = [f]

-- | Split conjuncts in many formulae at once
splitFormulae :: [Formula q v] -> [Formula q v]
splitFormulae = concatMap splitFormula


-- Clause types

axiom :: ClType
axiom = Axiom

lemma :: ClType
lemma = Lemma

hypothesis :: ClType
hypothesis = Hypothesis

definition :: ClType
definition = Definition

conjecture :: ClType
conjecture = Conjecture

negatedConjecture :: ClType
negatedConjecture = NegatedConjecture

question :: ClType
question = Question

-- Making many clauses
axioms :: [Formula q v] -> [Clause q v]
axioms = map (clause axiom)

definitions :: [Formula q v] -> [Clause q v]
definitions = map (clause definition)
