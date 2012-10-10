{-# LANGUAGE ParallelListComp #-}
{-

    Variable names that can be quantified over in axioms.

-}
module Halo.Names ( f, g, x, fTm, gTm, xTm, r, rTm, varNames ) where

import Id
import Name
import SrcLoc
import TysPrim
import Unique

import Halo.FOL.Abstract

import Control.Monad

-- | A bunch of variable names to quantify over
varNames :: [Var]
f,g,x :: Var
f:g:x:varNames =
    [ mkLocalId
        (mkInternalName (mkUnique 'z' i) (mkOccName varName n) wiredInSrcSpan)
        anyTy
    | i <- [0..]
    | n <- ["f","g","x"] ++ ([1..] >>= flip replicateM "xyzwvu")
    ]

-- | Terms with some fixed names 'f', 'g', 'x'
fTm,gTm,xTm :: VTerm
[fTm,gTm,xTm] = map qvar [f,g,x]

-- | Result term
-- Since we are using 'z' and 'fgxyzwvu' for ordinary variables,
-- I will use 'r' for the results of evaluation (rhs of eval predicate)
r :: Var
r = mkLocalId 
     (mkInternalName (mkUnique 'r' 0) (mkOccName varName "r") wiredInSrcSpan) anyTy

rTm :: VTerm
rTm = qvar r