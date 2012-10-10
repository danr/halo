{-# LANGUAGE NamedFieldPuns #-}
{-

    Make a pointer subtheory

-}
module Halo.Pointer where

import Id

import Halo.FOL.Abstract

import Halo.Conf
import Halo.Names ( varNames )
import Halo.Subtheory

-- | Makes a pointer to a constructor or function, given its arity
mkPtr :: HaloConf -> Var -> Int -> Subtheory s
mkPtr HaloConf{ext_eq} h arity = Subtheory
    { provides    = Pointer h
    , depends     = AppOnMin : [ ExtensionalEquality | ext_eq ]
    , description = "Pointer axiom to " ++ show h
    , formulae    =
        let lhs = apps (ptr h) as'
            rhs = funOrConApp h as'
        in  [qforall as $ {- ors [min' lhs,min' rhs] ==> -} lhs === rhs]
                            -- ^ new dimitrios' style
    }
  where
    as  = take arity varNames
    as' = map qvar as
