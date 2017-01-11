-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module is for writing generic functions on algebraic data types
-- of kind @*@. These data types must be an instance of the `Generic` type
-- class, which can be derived.
--
-----------------------------------------------------------------------------
{-# LANGUAGE
    RankNTypes
  , TypeFamilies
  , ConstraintKinds
  , FlexibleContexts
  #-}
module Generics.OneLiner (
  -- * Producing values
  create, createA, ctorIndex,
  -- * Traversing values
  gmap, gfoldMap, gtraverse,
  -- * Combining values
  gzipWith, mzipWith, zipWithA,
  -- * Consuming values
  consume,
  -- * Single constructor functions
  op0, op1, op2, algebra,
  -- * Generic programming with profunctors
  GenericRecordProfunctor(..), GenericNonEmptyProfunctor(..), GenericProfunctor(..), generic, nonEmpty, record,
  -- * Types
  ADT, ADTRecord, ADTNonEmpty, CtorCount, Constraints, For(..)
) where

import GHC.Generics
import Control.Applicative
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Functor.Contravariant.Divisible
import Data.Profunctor
import Data.Tagged
import Generics.OneLiner.Internal


-- | Create a value (one for each constructor), given how to construct the components.
--
-- @
-- `minBound` = `head` `$` `create` (`For` :: `For` `Bounded`) [`minBound`]
-- `maxBound` = `last` `$` `create` (`For` :: `For` `Bounded`) [`maxBound`]
-- @
create :: (ADT t, Constraints t c)
       => for c -> (forall s. c s => [s]) -> [t]
create for f = runJoker $ generic for $ Joker f

-- | Create a value (one for each constructor), given how to construct the components, under an applicative effect.
--
-- Here's how to implement `get` from the `binary` package:
--
-- @
-- get = getWord8 `>>=` \\ix -> `createA` (`For` :: `For` Binary) [get] `!!` `fromEnum` ix
-- @
createA :: (ADT t, Constraints t c, Applicative f)
        => for c -> (forall s. c s => [f s]) -> [f t]
createA for f = getCompose $ runJoker $ generic for $ Joker $ Compose f

-- | Generate ways to consume values of type `t`. This is the contravariant version of `createA`.
consume :: (ADT t, Constraints t c, Decidable f)
        => for c -> (forall s. c s => f s) -> f t
consume for f = runClown $ generic for $ Clown f



-- | Map over a structure, updating each component.
gmap :: (ADT t, Constraints t c)
     => for c -> (forall s. c s => s -> s) -> t -> t
gmap = generic

-- | Map each component of a structure to a monoid, and combine the results.
--
-- If you have a class `Size`, which measures the size of a structure, then this could be the default implementation:
--
-- @
-- size = `succ` `.` `getSum` `.` `gfoldMap` (`For` :: `For` Size) (`Sum` `.` size)
-- @
gfoldMap :: (ADT t, Constraints t c, Monoid m)
         => for c -> (forall s. c s => s -> m) -> t -> m
gfoldMap for f = getConst . gtraverse for (Const . f)

-- | Map each component of a structure to an action, evaluate these actions from left to right, and collect the results.
gtraverse :: (ADT t, Constraints t c, Applicative f)
          => for c -> (forall s. c s => s -> f s) -> t -> f t
gtraverse for f = runStar $ generic for $ Star f

-- | Combine two values by combining each component of the structures with the given function.
-- Returns `Nothing` if the constructors don't match.
gzipWith :: (ADT t, Constraints t c)
         => for c -> (forall s. c s => s -> s -> Maybe s) -> t -> t -> Maybe t
gzipWith for f l r = runIdentity <$> zipWithA for (\x y -> Identity <$> f x y) l r

-- | Combine two values by combining each component of the structures to a monoid, and combine the results.
-- Returns `mempty` if the constructors don't match.
--
-- @
-- `compare` s t = `compare` (`ctorIndex` s) (`ctorIndex` t) `<>` `mzipWith` (`For` :: `For` `Ord`) `compare` s t
-- @
mzipWith :: (ADT t, Constraints t c, Monoid m)
         => for c -> (forall s. c s => s -> s -> m) -> t -> t -> m
mzipWith for f l r = maybe mempty getConst $ zipWithA for (\x y -> Just . Const $ f x y) l r

-- | Combine two values by combining each component of the structures with the given function, under an applicative effect.
-- Returns `Nothing` if the constructors don't match.
zipWithA :: (ADT t, Constraints t c, Applicative f)
         => for c -> (forall s. c s => s -> s -> Maybe (f s)) -> t -> t -> Maybe (f t)
zipWithA for f = runZip $ generic for $ Zip f

newtype Zip f a b = Zip { runZip :: a -> a -> Maybe (f b) }
instance Functor f => Profunctor (Zip f) where
  dimap f g (Zip h) = Zip $ \a1 a2 -> fmap (fmap g) (h (f a1) (f a2))
instance Applicative f => GenericRecordProfunctor (Zip f) where
  unit = Zip . const $ Just . pure
  mult (Zip f) (Zip g) = Zip $ \(al :*: ar) (bl :*: br) -> liftA2 (:*:) <$> f al bl <*> g ar br
instance Applicative f => GenericNonEmptyProfunctor (Zip f) where
  plus (Zip f) (Zip g) = Zip h where
    h (L1 a) (L1 b) = fmap (fmap L1) (f a b)
    h (R1 a) (R1 b) = fmap (fmap R1) (g a b)
    h _ _ = Nothing
instance Applicative f => GenericProfunctor (Zip f) where
  zero = Zip . const $ Just . pure


-- | Implement a nullary operator by calling the operator for each component.
--
-- @
-- `mempty` = `op0` (`For` :: `For` `Monoid`) `mempty`
-- `fromInteger` i = `op0` (`For` :: `For` `Num`) (`fromInteger` i)
-- @
op0 :: (ADTRecord t, Constraints t c)
    => for c -> (forall s. c s => s) -> t
op0 for f = unTagged $ record for $ Tagged f

-- | Implement a unary operator by calling the operator on the components.
-- This is here for consistency, it is the same as `gmap`.
--
-- @
-- `negate` = `op1` (`For` :: `For` `Num`) `negate`
-- @
op1 :: (ADTRecord t, Constraints t c)
     => for c -> (forall s. c s => s -> s) -> t -> t
op1 = record

-- | Implement a binary operator by calling the operator on the components.
--
-- @
-- `mappend` = `op2` (`For` :: `For` `Monoid`) `mappend`
-- (`+`) = `op2` (`For` :: `For` `Num`) (`+`)
-- @
op2 :: (ADTRecord t, Constraints t c)
    => for c -> (forall s. c s => s -> s -> s) -> t -> t -> t
op2 for f l r = algebra for (\(Pair a b) -> f a b) (Pair l r)

data Pair a = Pair a a
instance Functor Pair where
  fmap f (Pair a b) = Pair (f a) (f b)

-- | Create an F-algebra, given an F-algebra for each of the components.
--
-- @
-- `op2` for f l r = `algebra` for (\\(Pair a b) -> f a b) (Pair l r)
-- @
algebra :: (ADTRecord t, Constraints t c, Functor f)
    => for c -> (forall s. c s => f s -> s) -> f t -> t
algebra for f = runCostar $ record for $ Costar f
