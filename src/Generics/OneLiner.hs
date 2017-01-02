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
  op0, op1, op2,
  -- * Generic programming with profunctors
  GenericProfunctor(..), generic,
  -- * Types
  ADT, ADTRecord, ADTNonEmpty, CtorCount, Constraints, For(..)
) where

import GHC.Generics
import Control.Applicative
import Data.Functor.Identity
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Profunctor
import Generics.OneLiner.Internal


newtype Zip f a b = Zip { runZip :: a -> a -> Maybe (f b) }
instance Functor f => Profunctor (Zip f) where
  dimap f g (Zip h) = Zip $ \a1 a2 -> fmap (fmap g) (h (f a1) (f a2))
instance Applicative f => GenericProfunctor (Zip f) where
  zero = Zip . const $ Just . pure
  unit = Zip . const $ Just . pure
  plus (Zip f) (Zip g) = Zip h where
    h (L1 a) (L1 b) = fmap (fmap L1) (f a b)
    h (R1 a) (R1 b) = fmap (fmap R1) (g a b)
    h _ _ = Nothing
  mult (Zip f) (Zip g) = Zip $ \(al :*: ar) (bl :*: br) -> liftA2 (:*:) <$> f al bl <*> g ar br

newtype Create f a b = Create { unCreate :: [f b] }
instance Functor f => Profunctor (Create f) where
  dimap _ f = Create . map (fmap f) . unCreate
instance Applicative f => GenericProfunctor (Create f) where
  zero = Create []
  unit = Create [pure U1]
  plus (Create l) (Create r) = Create $ map (fmap L1) l ++ map (fmap R1) r
  mult (Create l) (Create r) = Create $ liftA2 (:*:) <$> l <*> r

newtype Consume f a b = Consume { unConsume :: f a }
instance Contravariant f => Profunctor (Consume f) where
  dimap f _ = Consume . contramap f . unConsume
instance Decidable f => GenericProfunctor (Consume f) where
  zero = Consume $ lose (\v -> v `seq` undefined)
  unit = Consume conquer
  plus (Consume f) (Consume g) = Consume $ choose h f g where
    h (L1 l) = Left l
    h (R1 r) = Right r
  mult (Consume f) (Consume g) = Consume $ divide (\(l :*: r) -> (l, r)) f g


-- | Create a value (one for each constructor), given how to construct the components.
--
-- @
-- `minBound` = `head` `$` `create` (`For` :: `For` `Bounded`) [`minBound`]
-- `maxBound` = `last` `$` `create` (`For` :: `For` `Bounded`) [`maxBound`]
-- @
create :: (ADT t, Constraints t c)
       => for c -> (forall s. c s => [s]) -> [t]
create for f = map runIdentity (createA for (Identity <$> f))

-- | Create a value (one for each constructor), given how to construct the components, under an applicative effect.
--
-- Here's how to implement `get` from the `binary` package:
--
-- @
-- get = getWord8 `>>=` \\ix -> `createA` (`For` :: `For` Binary) [get] `!!` `fromEnum` ix
-- @
createA :: (ADT t, Constraints t c, Applicative f)
        => for c -> (forall s. c s => [f s]) -> [f t]
createA for f = unCreate $ generic for (Create f)

-- | Generate ways to consume values of type `t`. This is the contravariant version of `createA`.
consume :: (ADT t, Constraints t c, Decidable f)
        => for c -> (forall s. c s => f s) -> f t
consume for f = unConsume $ generic for (Consume f)



-- | Map over a structure, updating each component.
gmap :: (ADT t, Constraints t c)
     => for c -> (forall s. c s => s -> s) -> t -> t
gmap for f = runIdentity . gtraverse for (Identity . f)

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
gtraverse for f = runStar $ generic for (Star f)

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
zipWithA for f = runZip $ generic for (Zip f)

-- | Implement a nullary operator by calling the operator for each component.
--
-- @
-- `mempty` = `op0` (`For` :: `For` `Monoid`) `mempty`
-- `fromInteger` i = `op0` (`For` :: `For` `Num`) (`fromInteger` i)
-- @
op0 :: (ADTRecord t, Constraints t c)
    => for c -> (forall s. c s => s) -> t
op0 for f = head $ create for [f]

-- | Implement a unary operator by calling the operator on the components.
-- This is here for consistency, it is the same as `gmap`.
--
-- @
-- `negate` = `op1` (`For` :: `For` `Num`) `negate`
-- @
op1 :: (ADTRecord t, Constraints t c)
     => for c -> (forall s. c s => s -> s) -> t -> t
op1 = gmap

-- | Implement a binary operator by calling the operator on the components.
--
-- @
-- `mappend` = `op2` (`For` :: `For` `Monoid`) `mappend`
-- (`+`) = `op2` (`For` :: `For` `Num`) (`+`)
-- @
op2 :: (ADTRecord t, Constraints t c)
    => for c -> (forall s. c s => s -> s -> s) -> t -> t -> t
op2 for f l r = case gzipWith for (\a b -> Just (f a b)) l r of
  Just t -> t
  Nothing -> error "op2: constructor mismatch should not be possible for ADTRecord"
