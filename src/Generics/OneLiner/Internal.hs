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
    GADTs
  , DataKinds
  , RankNTypes
  , LambdaCase
  , TypeFamilies
  , TypeOperators
  , ConstraintKinds
  , FlexibleContexts
  , ScopedTypeVariables
  , UndecidableInstances
  #-}
module Generics.OneLiner.Internal where

import GHC.Generics
import GHC.Types (Constraint)
import GHC.TypeLits
import Data.Proxy
import Data.Profunctor

type family Constraints' (t :: * -> *) (c :: * -> Constraint) :: Constraint
type instance Constraints' V1 c = ()
type instance Constraints' U1 c = ()
type instance Constraints' (f :+: g) c = (Constraints' f c, Constraints' g c)
type instance Constraints' (f :*: g) c = (Constraints' f c, Constraints' g c)
type instance Constraints' (M1 i t f) c = Constraints' f c
type instance Constraints' (K1 i a) c = c a

class ADT' (t :: * -> *) where
  type CtorCount' t :: Nat
  type CtorCount' t = 1
  ctorIndex' :: t x -> Int
  ctorIndex' _ = 0
  ctorCount :: proxy t -> Int
  ctorCount _ = 1

  p :: (Constraints' t c, GenericProfunctor p)
    => for c -> (forall s. c s => p s s) -> p (t x) (t x)

instance ADT' V1 where
  type CtorCount' V1 = 0
  ctorCount _ = 0
  p _ _ = zero

instance (ADT' f, ADT' g) => ADT' (f :+: g) where
  type CtorCount' (f :+: g) = CtorCount' f + CtorCount' g
  ctorIndex' (L1 l) = ctorIndex' l
  ctorIndex' (R1 r) = ctorCount (Proxy :: Proxy f) + ctorIndex' r
  ctorCount _ = ctorCount (Proxy :: Proxy f) + ctorCount (Proxy :: Proxy g)
  p for f = plus (p for f) (p for f)

instance ADT' U1 where
  p _ _ = unit

instance (ADT' f, ADT' g) => ADT' (f :*: g) where
  p for f = mult (p for f) (p for f)

instance ADT' (K1 i v) where
  p _ = dimap unK1 K1

instance ADT' f => ADT' (M1 i t f) where
  type CtorCount' (M1 i t f) = CtorCount' f
  ctorIndex' = ctorIndex' . unM1
  ctorCount _ = ctorCount (Proxy :: Proxy f)
  p for f = dimap unM1 M1 (p for f)


class Profunctor p => GenericProfunctor p where
  zero :: p (V1 a) (V1 a)
  unit :: p (U1 a) (U1 a)
  plus :: p (f a) (f' a) -> p (g a) (g' a) -> p ((f :+: g) a) ((f' :+: g') a)
  mult :: p (f a) (f' a) -> p (g a) (g' a) -> p ((f :*: g) a) ((f' :*: g') a)

instance Applicative f => GenericProfunctor (Star f) where
  zero = Star pure
  unit = Star pure
  plus (Star f) (Star g) = Star $ \case
    L1 l -> L1 <$> f l
    R1 r -> R1 <$> g r
  mult (Star f) (Star g) = Star $ \(l :*: r) -> (:*:) <$> f l <*> g r

-- | All the above functions have been implemented using this single function,
-- using different `profunctor`s.
generic :: (ADT t, Constraints t c, GenericProfunctor p)
        => for c -> (forall s. c s => p s s) -> p t t
generic for f = dimap from to $ p for f

-- | `Constraints` is a constraint type synonym, containing the constraint requirements for an instance for `t` of class `c`.
-- It requires an instance of class `c` for each component of `t`.
type Constraints t c = Constraints' (Rep t) c

-- | `ADT` is a constraint type synonym. The `Generic` instance can be derived,
-- and any generic representation will be an instance of `ADT'`.
type ADT t = (Generic t, ADT' (Rep t))

-- | `CtorCount` is the number of constructors of a type at the type level.
-- F.e. if you want to require that a type has at least two constructors,
-- you can add the constraint @(2 `GHC.TypeLits.<=` `CtorCount` t)@.
type CtorCount t = CtorCount' (Rep t)

-- | `ADTRecord` is a constraint type synonym. An instance is an `ADT` with *exactly* one constructor.
type ADTRecord t = (ADT t, 1 ~ CtorCount t)

-- | `ADTNonEmpty` is a constraint type synonym. An instance is an `ADT` with *at least* one constructor.
type ADTNonEmpty t = (ADT t, 1 <= CtorCount t)

-- | Tell the compiler which class we want to use in the traversal. Should be used like this:
--
-- > (For :: For Show)
--
-- Where @Show@ can be any class.
data For (c :: * -> Constraint) = For

-- | Get the index in the lists returned by `create` and `createA` of the constructor of the given value.
--
-- For example, this is the implementation of `put` that generates the binary data that
-- the above implentation of `get` expects:
--
-- @
-- `put` t = `putWord8` (`toEnum` (`ctorIndex` t)) `<>` `gfoldMap` (`For` :: `For` `Binary`) `put` t
-- @
ctorIndex :: ADT t => t -> Int
ctorIndex = ctorIndex' . from
