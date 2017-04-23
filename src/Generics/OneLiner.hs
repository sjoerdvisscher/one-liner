-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- All functions without postfix are for instances of `Generic`, and functions
-- with postfix `1` are for instances of `Generic1` (with kind @* -> *@) which
-- get an extra argument to specify how to deal with the parameter.
-- The function `create_` does not require any such instance, but must be given
-- a constructor explicitly.
-----------------------------------------------------------------------------
{-# LANGUAGE
    RankNTypes
  , Trustworthy
  , TypeFamilies
  , ConstraintKinds
  , FlexibleContexts
  #-}
module Generics.OneLiner (
  -- * Producing values
  create, createA, ctorIndex,
  create1, createA1, ctorIndex1,
  createA_,
  -- * Traversing values
  gmap, gfoldMap, gtraverse,
  gmap1, gfoldMap1, gtraverse1,
  -- * Combining values
  mzipWith, zipWithA,
  mzipWith1, zipWithA1,
  -- * Consuming values
  consume, consume1,
  -- * Functions for records
  -- | These functions only work for single constructor data types.
  nullaryOp, unaryOp, binaryOp, createA', algebra, dialgebra,
  createA1', gcotraverse1,
  -- * Generic programming with profunctors
  -- | All the above functions have been implemented using these functions,
  -- using different `profunctor`s.
  GenericRecordProfunctor(..),
  GenericNonEmptyProfunctor(..),
  GenericProfunctor(..), generic, generic1,
  -- * Types
  ADT, Constraints,
  ADT1, Constraints1,
  For(..), AnyType,
  FunConstraints
) where

import GHC.Generics
import Control.Applicative
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
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
--
-- `create` is `createA` specialized to lists.
create :: (ADT t (Joker []), Constraints t c)
       => for c -> (forall s. c s => [s]) -> [t]
create = createA

-- | Create a value (one for each constructor), given how to construct the components, under an applicative effect.
--
-- Here's how to implement `get` from the `binary` package, first encoding the
-- constructor in a byte:
--
-- @
-- get = getWord8 `>>=` \\ix -> `getCompose` (`createA` (`For` :: `For` Binary) (`Compose` [get])) `!!` `fromEnum` ix
-- @
--
-- `createA` is `generic` specialized to `Joker`.
createA :: (ADT t (Joker f), Constraints t c)
        => for c -> (forall s. c s => f s) -> f t
createA for f = runJoker $ generic for $ Joker f

-- | Generate ways to consume values of type `t`. This is the contravariant version of `createA`.
--
-- `consume` is `generic` specialized to `Clown`.
consume :: (ADT t (Clown f), Constraints t c)
        => for c -> (forall s. c s => f s) -> f t
consume for f = runClown $ generic for $ Clown f

-- | `create1` is `createA1` specialized to lists.
create1 :: (ADT1 t (Joker []), Constraints1 t c)
        => for c -> (forall b s. c s => [b] -> [s b]) -> [a] -> [t a]
create1 = createA1

-- | `createA1` is `generic1` specialized to `Joker`.
createA1 :: (ADT1 t (Joker f), Constraints1 t c)
         => for c -> (forall b s. c s => f b -> f (s b)) -> f a -> f (t a)
createA1 for f = dimap Joker runJoker $ generic1 for $ dimap runJoker Joker f

-- | Create a value, given a constructor (or a function) and
-- how to construct its components, under an applicative effect.
--
-- For example, this is the implementation of `Test.QuickCheck.arbitrary` for a
-- type with a single constructor (e.g., quadruples @(,,,)@).
--
-- @
-- arbitrary = `createA_` (`For` :: `For` Arbitrary) arbitrary (,,,)
-- @
createA_ :: (FunConstraints t c, Applicative f)
         => for c -> (forall s. c s => f s) -> t -> f (Result t)
createA_ for run = autoApply for run . pure

-- | `consume1` is `generic1` specialized to `Clown`.
consume1 :: (ADT1 t (Clown f), Constraints1 t c)
         => for c -> (forall b s. c s => f b -> f (s b)) -> f a -> f (t a)
consume1 for f = dimap Clown runClown $ generic1 for $ dimap runClown Clown f


-- | Map over a structure, updating each component.
--
-- `gmap` is `generic` specialized to @(->)@.
gmap :: (ADT t (->), Constraints t c)
     => for c -> (forall s. c s => s -> s) -> t -> t
gmap = generic

-- | Map each component of a structure to an element of a monoid, and combine the results.
--
-- If you have a class `Size`, which measures the size of a structure, then this could be the default implementation:
--
-- @
-- size = `succ` `.` `getSum` `.` `gfoldMap` (`For` :: `For` Size) (`Sum` `.` size)
-- @
--
-- `gfoldMap` is `gtraverse` specialized to `Const`.
gfoldMap :: (ADT t (Star (Const m)), Constraints t c)
         => for c -> (forall s. c s => s -> m) -> t -> m
gfoldMap for f = getConst . gtraverse for (Const . f)

-- | Map each component of a structure to an action, evaluate these actions from left to right, and collect the results.
--
-- `gtraverse` is `generic` specialized to `Star`.
gtraverse :: (ADT t (Star f), Constraints t c)
          => for c -> (forall s. c s => s -> f s) -> t -> f t
gtraverse for f = runStar $ generic for $ Star f

-- |
-- @
-- fmap = `gmap1` (`For` :: `For` `Functor`) `fmap`
-- @
--
-- `gmap1` is `generic1` specialized to @(->)@.
gmap1 :: (ADT1 t (->), Constraints1 t c)
     => for c -> (forall d e s. c s => (d -> e) -> s d -> s e) -> (a -> b) -> t a -> t b
gmap1 = generic1

-- |
-- @
-- foldMap = `gfoldMap1` (`For` :: `For` `Foldable`) `foldMap`
-- @
--
-- `gfoldMap1` is `gtraverse1` specialized to `Const`.
gfoldMap1 :: (ADT1 t (Star (Const m)), Constraints1 t c)
          => for c -> (forall s b. c s => (b -> m) -> s b -> m) -> (a -> m) -> t a -> m
gfoldMap1 for f = dimap (Const .) (getConst .) $ gtraverse1 for $ dimap (getConst .) (Const .) f

-- |
-- @
-- traverse = `gtraverse1` (`For` :: `For` `Traversable`) `traverse`
-- @
--
-- `gtraverse1` is `generic1` specialized to `Star`.
gtraverse1 :: (ADT1 t (Star f), Constraints1 t c)
           => for c -> (forall d e s. c s => (d -> f e) -> s d -> f (s e)) -> (a -> f b) -> t a -> f (t b)
gtraverse1 for f = dimap Star runStar $ generic1 for $ dimap runStar Star f

-- | Combine two values by combining each component of the structures to a monoid, and combine the results.
-- Returns `mempty` if the constructors don't match.
--
-- @
-- `compare` s t = `compare` (`ctorIndex` s) (`ctorIndex` t) `<>` `mzipWith` (`For` :: `For` `Ord`) `compare` s t
-- @
--
-- `mzipWith` is `zipWithA` specialized to @`Compose` `Maybe` (`Const` m)@
mzipWith :: (ADT t (Zip (Compose Maybe (Const m))), Constraints t c, Monoid m)
         => for c -> (forall s. c s => s -> s -> m) -> t -> t -> m
mzipWith for f = outm2 $ zipWithA for $ inm2 f

-- | Combine two values by combining each component of the structures with the given function, under an applicative effect.
-- Returns `empty` if the constructors don't match.
zipWithA :: (ADT t (Zip f), Constraints t c)
         => for c -> (forall s. c s => s -> s -> f s) -> t -> t -> f t
zipWithA for f = runZip $ generic for $ Zip f

-- |
-- @
-- liftCompare = mzipWith1 (For :: For Ord1) liftCompare
-- @
--
-- `mzipWith1` is `zipWithA1` specialized to @`Compose` `Maybe` (`Const` m)@
mzipWith1 :: (ADT1 t (Zip (Compose Maybe (Const m))), Constraints1 t c, Monoid m)
          => for c -> (forall s b. c s => (b -> b -> m) -> s b -> s b -> m)
          -> (a -> a -> m) -> t a -> t a -> m
mzipWith1 for f = dimap inm2 outm2 $ zipWithA1 for $ dimap outm2 inm2 f

zipWithA1 :: (ADT1 t (Zip f), Constraints1 t c)
          => for c -> (forall d e s. c s => (d -> d -> f e) -> s d -> s d -> f (s e))
          -> (a -> a -> f b) -> t a -> t a -> f (t b)
zipWithA1 for f = dimap Zip runZip $ generic1 for $ dimap runZip Zip f


-- | Implement a nullary operator by calling the operator for each component.
--
-- @
-- `mempty` = `nullaryOp` (`For` :: `For` `Monoid`) `mempty`
-- `fromInteger` i = `nullaryOp` (`For` :: `For` `Num`) (`fromInteger` i)
-- @
--
-- `nullaryOp` is `generic` specialized to `Tagged`.
nullaryOp :: (ADT t Tagged, Constraints t c)
          => for c -> (forall s. c s => s) -> t
nullaryOp for f = unTagged $ generic for $ Tagged f

-- | Implement a unary operator by calling the operator on the components.
-- This is here for consistency, it is the same as `generic` and `gmap`.
--
-- @
-- `negate` = `unaryOp` (`For` :: `For` `Num`) `negate`
-- @
unaryOp :: (ADT t (->), Constraints t c)
        => for c -> (forall s. c s => s -> s) -> t -> t
unaryOp = generic

-- | Implement a binary operator by calling the operator on the components.
--
-- @
-- `mappend` = `binaryOp` (`For` :: `For` `Monoid`) `mappend`
-- (`+`) = `binaryOp` (`For` :: `For` `Num`) (`+`)
-- @
--
-- `binaryOp` is `algebra` specialized to pairs.
binaryOp :: (ADT t (Costar Pair), Constraints t c)
         => for c -> (forall s. c s => s -> s -> s) -> t -> t -> t
binaryOp for f = algebra for (\(Pair a b) -> f a b) .: Pair

-- | 'createA'' is the same as 'createA'. For backwards compatibility.
createA' :: (ADT t (Joker f), Constraints t c)
        => for c -> (forall s. c s => f s) -> f t
createA' = createA

data Pair a = Pair a a
instance Functor Pair where
  fmap f (Pair a b) = Pair (f a) (f b)

-- | Create an F-algebra, given an F-algebra for each of the components.
--
-- @
-- `binaryOp` for f l r = `algebra` for (\\(Pair a b) -> f a b) (Pair l r)
-- @
--
-- `algebra` is `generic` specialized to `Costar`.
algebra :: (ADT t (Costar f), Constraints t c)
        => for c -> (forall s. c s => f s -> s) -> f t -> t
algebra for f = runCostar $ generic for $ Costar f

-- | `dialgebra` is `generic` specialized to @`Biff` (->)@.
dialgebra :: (ADT t (Biff (->) f g), Constraints t c)
        => for c -> (forall s. c s => f s -> g s) -> f t -> g t
dialgebra for f = runBiff $ generic for $ Biff f

-- | `createA1'` is the same as `createA1`. For backwards compatibility.
createA1' :: (ADT1 t (Joker f), Constraints1 t c)
          => for c -> (forall b s. c s => f b -> f (s b)) -> f a -> f (t a)
createA1' = createA1

-- |
--
-- @
-- cotraverse = `gcotraverse1` (`For` :: `For` `Distributive`) `cotraverse`
-- @
--
-- `gcotraverse1` is `generic1` specialized to `Costar`.
gcotraverse1 :: (ADT1 t (Costar f), Constraints1 t c)
             => for c -> (forall d e s. c s => (f d -> e) -> f (s d) -> s e) -> (f a -> b) -> f (t a) -> t b
gcotraverse1 for f p = runCostar $ generic1 for (Costar . f . runCostar) (Costar p)
