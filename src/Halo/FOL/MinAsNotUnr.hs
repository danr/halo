module Halo.FOL.MinAsNotUnr ( minAsNotUnr ) where

import Halo.FOL.Internals.Internals
import Halo.FOL.Abstract
import Halo.FOL.Operations
import Halo.PrimCon

import Data.Generics.Geniplate

minAsNotUnr :: VClause -> VClause
minAsNotUnr = clauseMapFormula $ transformBi $ \f -> case f of
    Pred Min [tm] -> tm =/= unr
    e             -> e
