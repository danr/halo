{-# LANGUAGE DeriveFunctor #-}

-- Removes all Min _AND_ MinRec

module Halo.FOL.RemoveMin(removeMins,removeMinsSubthy) where

import Halo.FOL.Internals.Internals
import Halo.FOL.Abstract

import Halo.Subtheory

import Data.Maybe
import Control.Applicative

data Rm a = Pure a | Top | Bot
  deriving (Show,Eq,Ord,Functor)

isTop :: Rm a -> Bool
isTop Top{} = True
isTop _     = False

isBot :: Rm a -> Bool
isBot Bot{} = True
isBot _     = False

rmTop :: Rm a -> Maybe a
rmTop (Pure a) = Just a
rmTop Top      = Nothing
rmTop Bot      = error "rmTop: on Bot"

rmBot :: Rm a -> Maybe a
rmBot (Pure a) = Just a
rmBot Top      = error "rmTop: on Top"
rmBot Bot      = Nothing

-- | Collapses lists, @collapse p x q y c xs@ is
--       * x if anything satisfies p
--       * y if list is empty after filtering with q
--       * c on the list filtered with q otherwise
collapse
    :: (a -> Bool)
    -- ^ If any satisfies this predicate,
    -> r
    -- ^ then return this
    -> (a -> Maybe b)
    -- ^ Then strip off all satisfying this,
    -> r
    -- ^ None left, return this
    -> ([b] -> r)
    -- ^ At least one left, then return this
    -> [a]
    -- ^ List to collapse
    -> r
    -- ^ Result
collapse p x q y c xs
    | any p xs  = x
    | otherwise = case mapMaybe q xs of
                      [] -> y
                      ys -> c ys

rmMin :: Formula q v -> Rm (Formula q v)
rmMin f = case f of
    Pred Min _    -> Top
    Pred MinRec _ -> Top

    Pred _ _      -> Pure f

    Equal{}     -> Pure f
    Unequal{}   -> Pure f

    And fs -> collapse isBot Bot rmTop Top (Pure . ands) (map rmMin fs)
    Or fs  -> collapse isTop Top rmBot Bot (Pure . ors)  (map rmMin fs)

    Implies f1 f2 -> case (rmMin f1,rmMin f2) of
        (Top,f2') -> f2'
        (Bot,_f2) -> Top
        (_f1,Top) -> Top
        (f1',Bot) -> fmap neg f1'
        (Pure f1',Pure f2') -> Pure (Implies f1' f2')

    Neg f1 -> case rmMin f1 of
        Top     -> Bot
        Bot     -> Top
        Pure f2 -> Pure (neg f2)

    Forall qs f' -> fmap (Forall qs) (rmMin f')
    Exists qs f' -> fmap (Exists qs) (rmMin f')


rmToMaybe :: Rm a -> Maybe a
rmToMaybe (Pure a) = Just a
rmToMaybe Top      = Nothing
rmToMaybe Bot      = error "RemoveMin: Internal error, \
                           \A contradiction arose when removing mins!"

mapCl :: Applicative f
      => (Formula q v -> f (Formula q' v'))
      -> Clause q v -> f (Clause q' v')
mapCl k (Clause s t f) = Clause s t <$> k f
mapCl _ (Comment s)    = pure (Comment s)

removeMins :: [Clause q v] -> [Clause q v]
removeMins = mapMaybe (mapCl (rmToMaybe . rmMin))

removeMinsSubthy :: Subtheory s -> Subtheory s
removeMinsSubthy s = s { formulae = mapMaybe (rmToMaybe . rmMin) (formulae s) }
