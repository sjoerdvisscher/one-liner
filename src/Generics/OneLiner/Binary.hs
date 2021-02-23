-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.Binary
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- These generic functions allow changing the types of the constant leaves.
-- They require type classes with 2 parameters, the first for the input type
-- and the second for the output type.
--
-- All functions without postfix are for instances of `Generic`, and functions
-- with postfix @1@ are for instances of `Generic1` (with kind @Type -> Type@) which
-- get an extra argument to specify how to deal with the parameter.
-- Functions with postfix @01@ are also for `Generic1` but they get yet another
-- argument that, like the `Generic` functions, allows handling of constant leaves.
-----------------------------------------------------------------------------
{-# LANGUAGE
    RankNTypes
  , LinearTypes
  , Trustworthy
  , TypeFamilies
  , ConstraintKinds
  , FlexibleContexts
  , TypeApplications
  , AllowAmbiguousTypes
  , ScopedTypeVariables
  #-}
module Generics.OneLiner.Binary
(
  -- * Traversing values
  gmap, gtraverse,
  glmap, gltraverse,
  gmap1, gtraverse1,
  glmap1, gltraverse1,
  -- * Combining values
  zipWithA, zipWithA1,
  -- * Functions for records
  -- | These functions only work for single constructor data types.
  unaryOp, binaryOp, algebra, dialgebra, gcotraverse1,
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
  GenericUnitProfunctor(..),
  GenericProductProfunctor(..),
  GenericSumProfunctor(..),
  GenericEmptyProfunctor(..),
  -- * Types
  ADT, ADTNonEmpty, ADTRecord, Constraints,
  ADT1, ADTNonEmpty1, ADTRecord1, Constraints1, Constraints01,
  FunConstraints, FunResult,
  AnyType
)
where

import Control.Applicative
import Data.Bifunctor.Biff
import Data.Profunctor
import Data.Profunctor.Kleisli.Linear
import Generics.OneLiner.Classes
import Generics.OneLiner.Internal
import qualified Data.Functor.Linear as DL
import qualified Control.Functor.Linear as CL

-- | Map over a structure, updating each component.
--
-- `gmap` is `generic` specialized to @(->)@.
gmap :: forall c t t'. (ADT t t', Constraints t t' c)
     => (forall s s'. c s s' => s -> s') -> t -> t'
gmap = generic @c
{-# INLINE gmap #-}

-- | Map over a structure linearly, updating each component.
--
-- `glmap` is `generic` specialized to the linear arrow.
glmap :: forall c t t'. (ADT t t', Constraints t t' c)
      => (forall s s'. c s s' => s %1-> s') -> t %1-> t'
glmap = generic @c
{-# INLINE glmap #-}

-- | Map each component of a structure to an action, evaluate these actions from left to right, and collect the results.
--
-- `gtraverse` is `generic` specialized to `Star`.
gtraverse :: forall c t t' f. (ADT t t', Constraints t t' c, Applicative f)
          => (forall s s'. c s s' => s -> f s') -> t -> f t'
gtraverse f = runStar $ generic @c $ Star f
{-# INLINE gtraverse #-}

-- | Map each component of a structure to an action linearly, evaluate these actions from left to right, and collect the results.
--
-- `gltraverse` is `generic` specialized to linear `Kleisli`.
gltraverse :: forall c t t' f. (ADT t t', Constraints t t' c, DL.Applicative f)
           => (forall s s'. c s s' => s %1-> f s') -> t %1-> f t'
gltraverse f = runKleisli $ generic @c $ Kleisli f
{-# INLINE gltraverse #-}

-- | `gmap1` is `generic1` specialized to @(->)@.
gmap1 :: forall c t t' a b. (ADT1 t t', Constraints1 t t' c)
      => (forall d e s s'. c s s' => (d -> e) -> s d -> s' e) -> (a -> b) -> t a -> t' b
gmap1 = generic1 @c
{-# INLINE gmap1 #-}

-- | `glmap1` is `generic1` specialized to the linear arrow.
glmap1 :: forall c t t' a b. (ADT1 t t', Constraints1 t t' c)
       => (forall d e s s'. c s s' => (d %1-> e) -> s d %1-> s' e) -> (a %1-> b) -> t a %1-> t' b
glmap1 = generic1 @c
{-# INLINE glmap1 #-}

-- | `gtraverse1` is `generic1` specialized to `Star`.
gtraverse1 :: forall c t t' f a b. (ADT1 t t', Constraints1 t t' c, Applicative f)
           => (forall d e s s'. c s s' => (d -> f e) -> s d -> f (s' e)) -> (a -> f b) -> t a -> f (t' b)
gtraverse1 f = dimap Star runStar $ generic1 @c $ dimap runStar Star f
{-# INLINE gtraverse1 #-}

-- | `gltraverse1` is `generic1` specialized to linear `Kleisli`.
gltraverse1 :: forall c t t' f a b. (ADT1 t t', Constraints1 t t' c, CL.Applicative f)
            => (forall d e s s'. c s s' => (d %1-> f e) -> s d %1-> f (s' e)) -> (a %1-> f b) -> t a %1-> f (t' b)
gltraverse1 f = dimap Kleisli runKleisli $ generic1 @c $ dimap runKleisli Kleisli f
{-# INLINE gltraverse1 #-}

-- | Combine two values by combining each component of the structures with the given function, under an applicative effect.
-- Returns `empty` if the constructors don't match.
--
-- `zipWithA` is `generic` specialized to `Zip`
zipWithA :: forall c t t' f. (ADT t t', Constraints t t' c, Alternative f)
         => (forall s s'. c s s' => s -> s -> f s') -> t -> t -> f t'
zipWithA f = runZip $ generic @c $ Zip f
{-# INLINE zipWithA #-}

-- | `zipWithA1` is `generic1` specialized to `Zip`
zipWithA1 :: forall c t t' f a b. (ADT1 t t', Constraints1 t t' c, Alternative f)
          => (forall d e s s'. c s s' => (d -> d -> f e) -> s d -> s d -> f (s' e))
          -> (a -> a -> f b) -> t a -> t a -> f (t' b)
zipWithA1 f = dimap Zip runZip $ generic1 @c $ dimap runZip Zip f
{-# INLINE zipWithA1 #-}

-- | Implement a unary operator by calling the operator on the components.
-- This is here for consistency, it is the same as `record`.
--
-- @
-- `negate` = `unaryOp` \@`Num` `negate`
-- @
unaryOp :: forall c t t'. (ADTRecord t t', Constraints t t' c)
        => (forall s s'. c s s' => s -> s') -> t -> t'
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
binaryOp :: forall c t t'. (ADTRecord t t', Constraints t t' c)
         => (forall s s'. c s s' => s -> s -> s') -> t -> t -> t'
binaryOp f = algebra @c (\(Pair a b) -> f a b) .: Pair
{-# INLINE binaryOp #-}

-- | Create an F-algebra, given an F-algebra for each of the components.
--
-- @
-- `binaryOp` f l r = `algebra` \@c (\\(Pair a b) -> f a b) (Pair l r)
-- @
--
-- `algebra` is `record` specialized to `Costar`.
algebra :: forall c t t' f. (ADTRecord t t', Constraints t t' c, Functor f)
        => (forall s s'. c s s' => f s -> s') -> f t -> t'
algebra f = runCostar $ record @c $ Costar f
{-# INLINE algebra #-}

-- | `dialgebra` is `record` specialized to @`Biff` (->)@.
dialgebra :: forall c t t' f g. (ADTRecord t t', Constraints t t' c, Functor f, Applicative g)
        => (forall s s'. c s s' => f s -> g s') -> f t -> g t'
dialgebra f = runBiff $ record @c $ Biff f
{-# INLINE dialgebra #-}

-- | `gcotraverse1` is `record1` specialized to `Costar`.
gcotraverse1 :: forall c t t' f a b. (ADTRecord1 t t', Constraints1 t t' c, Functor f)
             => (forall d e s s'. c s s' => (f d -> e) -> f (s d) -> s' e) -> (f a -> b) -> f (t a) -> t' b
gcotraverse1 f p = runCostar $ record1 @c (Costar . f . runCostar) (Costar p)
{-# INLINE gcotraverse1 #-}