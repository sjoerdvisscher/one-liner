-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.Internal
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------

{-# LANGUAGE
    PolyKinds
  , RankNTypes
  , TypeFamilies
  , ConstraintKinds
  , FlexibleContexts
  , TypeApplications
  , FlexibleInstances
  , AllowAmbiguousTypes
  , ScopedTypeVariables
  , MultiParamTypeClasses
  , UndecidableSuperClasses
  #-}

module Generics.OneLiner.Internal.Unary where

import Data.Kind (Constraint)
import qualified Generics.OneLiner.Internal as I

-- | Type-level 'join', of kind @(k -> k -> k') -> k -> k'@.
type J f a = f a a

-- | Constraint-level 'duplicate', of kind @(k -> Constraint) -> k -> k -> Constraint
class (c a, a ~ b) => D (c :: k -> Constraint) a b
instance (c a, a ~ b) => D c a b

type Constraints t c = I.Constraints t t (D c)
type Constraints1 t c = I.Constraints1 t t (D c)
type Constraints01 t c0 c1 = I.Constraints01 t t (D c0) (D c1)
type Constraints' t c c1 = I.Constraints' t t (D c) (D c1)

type ADTRecord t = (I.ADTRecord t t, Constraints t AnyType)
type ADTRecord1 t = (I.ADTRecord1 t t, Constraints1 t AnyType)
type ADTNonEmpty t = (I.ADTNonEmpty t t, Constraints t AnyType)
type ADTNonEmpty1 t = (I.ADTNonEmpty1 t t, Constraints1 t AnyType)
type ADT t = (I.ADT t t, Constraints t AnyType)
type ADT1 t = (I.ADT1 t t, Constraints1 t AnyType)

record :: forall c p t. (ADTRecord t, Constraints t c, I.GenericRecordProfunctor p)
       => (forall s. c s => p s s) -> p t t
record = I.record @(D c)
{-# INLINE record #-}

record1 :: forall c p t a b. (ADTRecord1 t, Constraints1 t c, I.GenericRecordProfunctor p)
        => (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
record1 = I.record1 @(D c)
{-# INLINE record1 #-}

record01 :: forall c0 c1 p t a b. (ADTRecord1 t, Constraints01 t c0 c1, I.GenericRecordProfunctor p)
         => (forall s. c0 s => p s s) -> (forall d e s. c1 s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
record01 = I.record01 @(D c0) @(D c1)
{-# INLINE record01 #-}

nonEmpty :: forall c p t. (ADTNonEmpty t, Constraints t c, I.GenericNonEmptyProfunctor p)
         => (forall s. c s => p s s) -> p t t
nonEmpty = I.nonEmpty @(D c)
{-# INLINE nonEmpty #-}

nonEmpty1 :: forall c p t a b. (ADTNonEmpty1 t, Constraints1 t c, I.GenericNonEmptyProfunctor p)
          => (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
nonEmpty1 = I.nonEmpty1 @(D c)
{-# INLINE nonEmpty1 #-}

nonEmpty01 :: forall c0 c1 p t a b. (ADTNonEmpty1 t, Constraints01 t c0 c1, I.GenericNonEmptyProfunctor p)
           => (forall s. c0 s => p s s) -> (forall d e s. c1 s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
nonEmpty01 = I.nonEmpty01 @(D c0) @(D c1)
{-# INLINE nonEmpty01 #-}

generic :: forall c p t. (ADT t, Constraints t c, I.GenericProfunctor p)
        => (forall s. c s => p s s) -> p t t
generic = I.generic @(D c) @p @t @t
{-# INLINE generic #-}

generic1 :: forall c p t a b. (ADT1 t, Constraints1 t c, I.GenericProfunctor p)
         => (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
generic1 = I.generic1 @(D c) @p @t @t
{-# INLINE generic1 #-}

generic01 :: forall c0 c1 p t a b. (ADT1 t, Constraints01 t c0 c1, I.GenericProfunctor p)
          => (forall s. c0 s => p s s) -> (forall d e s. c1 s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
generic01 = I.generic01 @(D c0) @(D c1)
{-# INLINE generic01 #-}

-- | Get the index in the lists returned by `create` and `createA` of the constructor of the given value.
--
-- For example, this is the implementation of `put` that generates the binary data that
-- the above implentation of `get` expects:
--
-- @
-- `put` t = `putWord8` (`toEnum` (`ctorIndex` t)) `<>` `gfoldMap` \@`Binary` `put` t
-- @
ctorIndex :: forall t. ADT t => t -> Int
ctorIndex = I.index $ I.generic @I.AnyType @_ @t @t (I.Ctor (const 0) 1)
{-# INLINE ctorIndex #-}

ctorIndex1 :: forall t a. ADT1 t => t a -> Int
ctorIndex1 = I.index $ I.generic1 @I.AnyType @_ @t @t (const $ I.Ctor (const 0) 1) (I.Ctor (const 0) 1)
{-# INLINE ctorIndex1 #-}

-- | Any type is instance of `AnyType`, you can use it with @\@`AnyType`@
-- if you don't actually need a class constraint.
class AnyType (a :: k)
instance AnyType (a :: k)

