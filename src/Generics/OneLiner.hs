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
-- with postfix @1@ are for instances of `Generic1` (with kind @Type -> Type@) which
-- get an extra argument to specify how to deal with the parameter.
-- Functions with postfix @01@ are also for `Generic1` but they get yet another
-- argument that, like the `Generic` functions, allows handling of constant leaves.
-- The function `createA_` does not require any such instance, but must be given
-- a constructor explicitly.
-----------------------------------------------------------------------------
{-# LANGUAGE
    RankNTypes
  , Trustworthy
  , LinearTypes
  , TypeFamilies
  , ConstraintKinds
  , FlexibleContexts
  , TypeApplications
  , AllowAmbiguousTypes
  , ScopedTypeVariables
  #-}
module Generics.OneLiner (
  -- * Producing values
  create, createA, ctorIndex,
  create1, createA1, ctorIndex1,
  createA_,
  -- * Traversing values
  gmap, gfoldMap, gtraverse,
  glmap, glfoldMap, gltraverse,
  gmap1, gfoldMap1, gtraverse1,
  glmap1, gltraverse1, gltraverse01,
  -- * Combining values
  mzipWith, mzipWith', zipWithA,
  mzipWith1, mzipWith1', zipWithA1,
  -- * Consuming values
  consume, consume1,
  -- * Functions for records
  -- | These functions only work for single constructor data types.
  nullaryOp, unaryOp, binaryOp, createA', algebra, dialgebra,
  createA1', gcotraverse1,
  -- * Generic programming with profunctors
  -- | All the above functions have been implemented using these functions,
  -- using different `profunctor`s.
  record, nonEmpty, generic,
  record1, nonEmpty1, generic1,
  record01, nonEmpty01, generic01,
  -- ** Classes
  GenericRecordProfunctor,
  GenericNonEmptyProfunctor,
  GenericProfunctor,
  Generic1Profunctor,
  GenericUnitProfunctor(..),
  GenericProductProfunctor(..),
  GenericSumProfunctor(..),
  GenericEmptyProfunctor(..),
  GenericConstantProfunctor(..),
  -- * Types
  ADT, ADTNonEmpty, ADTRecord, Constraints,
  ADT1, ADTNonEmpty1, ADTRecord1, Constraints1, Constraints01,
  FunConstraints, FunResult,
  AnyType
  ) where

import Control.Applicative
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Functor.Compose
import Data.Functor.Contravariant.Divisible
import qualified Control.Functor.Linear as CL
import qualified Data.Functor.Linear as DL
import qualified Data.Monoid.Linear as Linear
import qualified Data.Unrestricted.Linear as Linear
import Data.Profunctor
import Data.Profunctor.Kleisli.Linear
import Data.Tagged
import Generics.OneLiner.Classes
import Generics.OneLiner.Internal (FunConstraints, FunResult, autoApply, Pair(..), (.:))
import Generics.OneLiner.Internal.Unary

-- | Create a value (one for each constructor), given how to construct the components.
--
-- @
-- `minBound` = `head` `$` `create` \@`Bounded` [`minBound`]
-- `maxBound` = `last` `$` `create` \@`Bounded` [`maxBound`]
-- @
--
-- `create` is `createA` specialized to lists.
create :: forall c t. (ADT t, Constraints t c)
       => (forall s. c s => [s]) -> [t]
create = createA @c
{-# INLINE create #-}

-- | Create a value (one for each constructor), given how to construct the components, under an applicative effect.
--
-- Here's how to implement `get` from the `binary` package, first encoding the
-- constructor in a byte:
--
-- @
-- get = getWord8 `>>=` \\ix -> `getCompose` (`createA` \@Binary (`Compose` [get])) `!!` `fromEnum` ix
-- @
--
-- `createA` is `generic` specialized to `Joker`.
createA :: forall c t f. (ADT t, Constraints t c, Alternative f)
        => (forall s. c s => f s) -> f t
createA f = runJoker $ generic @c $ Joker f
{-# INLINE createA #-}

-- | Generate ways to consume values of type `t`. This is the contravariant version of `createA`.
--
-- `consume` is `generic` specialized to `Clown`.
consume :: forall c t f. (ADT t, Constraints t c, Decidable f)
        => (forall s. c s => f s) -> f t
consume f = runClown $ generic @c $ Clown f
{-# INLINE consume #-}

-- | `create1` is `createA1` specialized to lists.
create1 :: forall c t a. (ADT1 t, Constraints1 t c)
        => (forall b s. c s => [b] -> [s b]) -> [a] -> [t a]
create1 = createA1 @c
{-# INLINE create1 #-}

-- | `createA1` is `generic1` specialized to `Joker`.
createA1 :: forall c t f a. (ADT1 t, Constraints1 t c, Alternative f)
         => (forall b s. c s => f b -> f (s b)) -> f a -> f (t a)
createA1 f = dimap Joker runJoker $ generic1 @c $ dimap runJoker Joker f
{-# INLINE createA1 #-}

-- | Create a value, given a constructor (or a function) and
-- how to construct its components, under an applicative effect.
--
-- For example, this is the implementation of `Test.QuickCheck.arbitrary` for a
-- type with a single constructor (e.g., quadruples @(,,,)@).
--
-- @
-- arbitrary = `createA_` \@`Arbitrary` arbitrary (,,,)
-- @
createA_ :: forall c t f. (FunConstraints c t, Applicative f)
         => (forall s. c s => f s) -> t -> f (FunResult t)
createA_ run = autoApply @c run . pure
{-# INLINE createA_ #-}

-- | `consume1` is `generic1` specialized to `Clown`.
consume1 :: forall c t f a. (ADT1 t, Constraints1 t c, Decidable f)
         => (forall b s. c s => f b -> f (s b)) -> f a -> f (t a)
consume1 f = dimap Clown runClown $ generic1 @c $ dimap runClown Clown f
{-# INLINE consume1 #-}


-- | Map over a structure, updating each component.
--
-- `gmap` is `generic` specialized to @(->)@.
gmap :: forall c t. (ADT t, Constraints t c)
     => (forall s. c s => s -> s) -> t -> t
gmap = generic @c
{-# INLINE gmap #-}

-- | Map over a structure linearly, updating each component.
--
-- `glmap` is `generic` specialized to the linear arrow.
glmap :: forall c t. (ADT t, Constraints t c)
     => (forall s. c s => s %1-> s) -> t %1-> t
glmap = generic @c
{-# INLINE glmap #-}

-- | Map each component of a structure to a monoid, and combine the results.
--
-- If you have a class `Size`, which measures the size of a structure, then this could be the default implementation:
--
-- @
-- size = `succ` `.` `getSum` `.` `gfoldMap` \@`Size` (`Sum` `.` size)
-- @
--
-- `gfoldMap` is `gtraverse` specialized to `Const`.
gfoldMap :: forall c t m. (ADT t, Constraints t c, Monoid m)
         => (forall s. c s => s -> m) -> t -> m
gfoldMap f = getConst . gtraverse @c (Const . f)
{-# INLINE gfoldMap #-}

-- | Map each component of a structure to a linear monoid, and combine the results.
--
-- For example. this could be the default implementation of `Linear.Consumable`:
--
-- @
-- consume = `glfoldMap` \@`Linear.Consumable` `Linear.consume`
-- @
--
-- `glfoldMap` is `gltraverse` specialized to `Const`.
glfoldMap :: forall c t m. (ADT t, Constraints t c, Linear.Monoid m)
          => (forall s. c s => s %1-> m) -> t %1-> m
glfoldMap f t = (\(Const c) -> c) (gltraverse @c (\x -> Const (f x)) t)
{-# INLINE glfoldMap #-}

-- | Map each component of a structure to an action, evaluate these actions from left to right, and collect the results.
--
-- `gtraverse` is `generic` specialized to `Star`.
gtraverse :: forall c t f. (ADT t, Constraints t c, Applicative f)
          => (forall s. c s => s -> f s) -> t -> f t
gtraverse f = runStar $ generic @c $ Star f
{-# INLINE gtraverse #-}

-- | Map each component of a structure to an action linearly, evaluate these actions from left to right, and collect the results.
--
-- For example. this could be the default implementations of `Linear.Dupable` and `Linear.Movable`:
--
-- @
-- dupV = `gltraverse` \@`Linear.Dupable` `Linear.dupV`
-- move = `gltraverse` \@`Linear.Movable` `Linear.move`
-- @
--
-- `gltraverse` is `generic` specialized to linear `Kleisli`.
gltraverse :: forall c t f. (ADT t, Constraints t c, DL.Applicative f)
           => (forall s. c s => s %1-> f s) -> t %1-> f t
gltraverse f = runKleisli $ generic @c $ Kleisli f
{-# INLINE gltraverse #-}

-- |
-- @
-- fmap = `gmap1` \@`Functor` `fmap`
-- @
--
-- `gmap1` is `generic1` specialized to @(->)@.
gmap1 :: forall c t a b. (ADT1 t, Constraints1 t c)
      => (forall d e s. c s => (d -> e) -> s d -> s e) -> (a -> b) -> t a -> t b
gmap1 = generic1 @c
{-# INLINE gmap1 #-}

-- |
-- @
-- fmap = `gmap1` \@`Linear.Functor` `Linear.fmap`
-- @
--
-- `glmap1` is `generic1` specialized to the linear arrow.
glmap1 :: forall c t a b. (ADT1 t, Constraints1 t c)
       => (forall d e s. c s => (d %1-> e) -> s d %1-> s e) -> (a %1-> b) -> t a %1-> t b
glmap1 = generic1 @c
{-# INLINE glmap1 #-}

-- |
-- @
-- foldMap = `gfoldMap1` \@`Foldable` `foldMap`
-- @
--
-- `gfoldMap1` is `gtraverse1` specialized to `Const`.
gfoldMap1 :: forall c t m a. (ADT1 t, Constraints1 t c, Monoid m)
          => (forall s b. c s => (b -> m) -> s b -> m) -> (a -> m) -> t a -> m
gfoldMap1 f = dimap (Const .) (getConst .) $ gtraverse1 @c $ dimap (getConst .) (Const .) f
{-# INLINE gfoldMap1 #-}

-- |
-- @
-- traverse = `gtraverse1` \@`Traversable` `traverse`
-- @
--
-- `gtraverse1` is `generic1` specialized to `Star`.
gtraverse1 :: forall c t f a b. (ADT1 t, Constraints1 t c, Applicative f)
           => (forall d e s. c s => (d -> f e) -> s d -> f (s e)) -> (a -> f b) -> t a -> f (t b)
gtraverse1 f = dimap Star runStar $ generic1 @c $ dimap runStar Star f
{-# INLINE gtraverse1 #-}

-- |
-- @
-- traverse = `gltraverse1` \@`DL.Traversable` `DL.traverse`
-- @
--
-- `gltraverse1` is `generic1` specialized to linear `Kleisli`.
gltraverse1 :: forall c t f a b. (ADT1 t, Constraints1 t c, CL.Applicative f)
            => (forall d e s. c s => (d %1-> f e) -> s d %1-> f (s e)) -> (a %1-> f b) -> t a %1-> f (t b)
gltraverse1 f = dimap Kleisli runKleisli $ generic1 @c $ dimap runKleisli Kleisli f
{-# INLINE gltraverse1 #-}

-- | `gltraverse01` is `generic01` specialized to linear `Kleisli`, requiring `Linear.Movable` for constants.
gltraverse01 :: forall c t f a b. (ADT1 t, Constraints01 t Linear.Movable c, DL.Applicative f)
             => (forall d e s. c s => (d %1-> f e) -> s d %1-> f (s e)) -> (a %1-> f b) -> t a %1-> f (t b)
gltraverse01 f = dimap Kleisli runKleisli $ generic01 @Linear.Movable @c (Kleisli (\a -> urpure (Linear.move a))) $ dimap runKleisli Kleisli f
{-# INLINE gltraverse01 #-}

urpure :: DL.Applicative f => Linear.Ur a %1-> f a
urpure (Linear.Ur a) = DL.pure a

-- | Combine two values by combining each component of the structures to a monoid, and combine the results.
-- Returns `mempty` if the constructors don't match.
--
-- @
-- `compare` s t = `compare` (`ctorIndex` s) (`ctorIndex` t) `<>` `mzipWith` \@`Ord` `compare` s t
-- @
--
-- `mzipWith` is `zipWithA` specialized to @`Compose` `Maybe` (`Const` m)@
mzipWith :: forall c t m. (ADT t, Constraints t c, Monoid m)
         => (forall s. c s => s -> s -> m) -> t -> t -> m
mzipWith = mzipWith' @c mempty
{-# INLINE mzipWith #-}

-- | Variant of `mzipWith` where you can choose the value which is returned
-- when the constructors don't match.
--
-- @
-- `compare` s t = `mzipWith'` \@`Ord` (`compare` (`ctorIndex` s) (`ctorIndex` t)) `compare` s t
-- @
mzipWith' :: forall c t m. (ADT t, Constraints t c, Monoid m)
          => m -> (forall s. c s => s -> s -> m) -> t -> t -> m
mzipWith' m f = outm2 m $ zipWithA @c $ inm2 f
{-# INLINE mzipWith' #-}

-- | Combine two values by combining each component of the structures with the given function, under an applicative effect.
-- Returns `empty` if the constructors don't match.
--
-- `zipWithA` is `generic` specialized to `Zip`
zipWithA :: forall c t f. (ADT t, Constraints t c, Alternative f)
         => (forall s. c s => s -> s -> f s) -> t -> t -> f t
zipWithA f = runZip $ generic @c $ Zip f
{-# INLINE zipWithA #-}

-- |
-- @
-- `liftCompare` = `mzipWith1` \@`Ord1` `liftCompare`
-- @
--
-- `mzipWith1` is `zipWithA1` specialized to @`Compose` `Maybe` (`Const` m)@
mzipWith1 :: forall c t m a. (ADT1 t, Constraints1 t c, Monoid m)
          => (forall s b. c s => (b -> b -> m) -> s b -> s b -> m)
          -> (a -> a -> m) -> t a -> t a -> m
mzipWith1 = mzipWith1' @c mempty
{-# INLINE mzipWith1 #-}

-- | Variant of `mzipWith1` where you can choose the value which is returned
-- when the constructors don't match.
mzipWith1' :: forall c t m a. (ADT1 t, Constraints1 t c, Monoid m)
           => m
           -> (forall s b. c s => (b -> b -> m) -> s b -> s b -> m)
           -> (a -> a -> m) -> t a -> t a -> m
mzipWith1' m f = dimap inm2 (outm2 m) $ zipWithA1 @c $ dimap (outm2 m) inm2 f
{-# INLINE mzipWith1' #-}

-- | `zipWithA1` is `generic1` specialized to `Zip`
zipWithA1 :: forall c t f a b. (ADT1 t, Constraints1 t c, Alternative f)
          => (forall d e s. c s => (d -> d -> f e) -> s d -> s d -> f (s e))
          -> (a -> a -> f b) -> t a -> t a -> f (t b)
zipWithA1 f = dimap Zip runZip $ generic1 @c $ dimap runZip Zip f
{-# INLINE zipWithA1 #-}

inm2 :: (t -> t -> m) -> t -> t -> Compose Maybe (Const m) a
inm2 f = Compose .: Just .: Const .: f
{-# INLINE inm2 #-}
outm2 :: Monoid m => m -> (t -> t -> Compose Maybe (Const m) a) -> t -> t -> m
outm2 z f = maybe z getConst .: getCompose .: f
{-# INLINE outm2 #-}

-- | Implement a nullary operator by calling the operator for each component.
--
-- @
-- `mempty` = `nullaryOp` \@`Monoid` `mempty`
-- `fromInteger` i = `nullaryOp` \@`Num` (`fromInteger` i)
-- @
--
-- `nullaryOp` is `record` specialized to `Tagged`.
nullaryOp :: forall c t. (ADTRecord t, Constraints t c)
          => (forall s. c s => s) -> t
nullaryOp f = unTagged $ record @c $ Tagged f
{-# INLINE nullaryOp #-}

-- | Implement a unary operator by calling the operator on the components.
-- This is here for consistency, it is the same as `record`.
--
-- @
-- `negate` = `unaryOp` \@`Num` `negate`
-- @
unaryOp :: forall c t. (ADTRecord t, Constraints t c)
        => (forall s. c s => s -> s) -> t -> t
unaryOp = record @c
{-# INLINE unaryOp #-}

-- | Implement a binary operator by calling the operator on the components.
--
-- @
-- `mappend` = `binaryOp` \@`Monoid` `mappend`
-- (`+`) = `binaryOp` \@`Num` (`+`)
-- @
--
-- `binaryOp` is `algebra` specialized to pairs.
binaryOp :: forall c t. (ADTRecord t, Constraints t c)
         => (forall s. c s => s -> s -> s) -> t -> t -> t
binaryOp f = algebra @c (\(Pair a b) -> f a b) .: Pair
{-# INLINE binaryOp #-}

-- | Create a value of a record type (with exactly one constructor), given
-- how to construct the components, under an applicative effect.
--
-- Here's how to implement `get` from the `binary` package:
--
-- @
-- get = `createA'` (`For` :: `For` Binary) get
-- @
--
-- `createA'` is `record` specialized to `Joker`.
createA' :: forall c t f. (ADTRecord t, Constraints t c, Applicative f)
         => (forall s. c s => f s) -> f t
createA' f = runJoker $ record @c $ Joker f
{-# INLINE createA' #-}

-- | Create an F-algebra, given an F-algebra for each of the components.
--
-- @
-- `binaryOp` f l r = `algebra` \@c (\\(Pair a b) -> f a b) (Pair l r)
-- @
--
-- `algebra` is `record` specialized to `Costar`.
algebra :: forall c t f. (ADTRecord t, Constraints t c, Functor f)
        => (forall s. c s => f s -> s) -> f t -> t
algebra f = runCostar $ record @c $ Costar f
{-# INLINE algebra #-}

-- | `dialgebra` is `record` specialized to @`Biff` (->)@.
dialgebra :: forall c t f g. (ADTRecord t, Constraints t c, Functor f, Applicative g)
        => (forall s. c s => f s -> g s) -> f t -> g t
dialgebra f = runBiff $ record @c $ Biff f
{-# INLINE dialgebra #-}

-- | `createA1'` is `record1` specialized to `Joker`.
createA1' :: forall c t f a. (ADTRecord1 t, Constraints1 t c, Applicative f)
         => (forall b s. c s => f b -> f (s b)) -> f a -> f (t a)
createA1' f = dimap Joker runJoker $ record1 @c $ dimap runJoker Joker f
{-# INLINE createA1' #-}

-- |
--
-- @
-- cotraverse = `gcotraverse1` \@`Distributive` `cotraverse`
-- @
--
-- `gcotraverse1` is `record1` specialized to `Costar`.
gcotraverse1 :: forall c t f a b. (ADTRecord1 t, Constraints1 t c, Functor f)
             => (forall d e s. c s => (f d -> e) -> f (s d) -> s e) -> (f a -> b) -> f (t a) -> t b
gcotraverse1 f p = runCostar $ record1 @c (Costar . f . runCostar) (Costar p)
{-# INLINE gcotraverse1 #-}
