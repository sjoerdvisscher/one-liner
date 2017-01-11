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
import Control.Applicative
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Functor.Contravariant.Divisible
import Data.Proxy
import Data.Profunctor
import Data.Tagged

type family Constraints' (t :: * -> *) (c :: * -> Constraint) :: Constraint
type instance Constraints' V1 c = ()
type instance Constraints' U1 c = ()
type instance Constraints' (f :+: g) c = (Constraints' f c, Constraints' g c)
type instance Constraints' (f :*: g) c = (Constraints' f c, Constraints' g c)
type instance Constraints' (M1 i t f) c = Constraints' f c
type instance Constraints' (K1 i a) c = c a

type family CtorCount' (t :: * -> *) :: Nat
type instance CtorCount' V1 = 0
type instance CtorCount' U1 = 1
type instance CtorCount' (f :+: g) = CtorCount' f + CtorCount' g
type instance CtorCount' (f :*: g) = 1
type instance CtorCount' (M1 i t f) = CtorCount' f
type instance CtorCount' (K1 i a) = 1

class ADT' (t :: * -> *) where
  ctorIndex' :: t x -> Int
  ctorIndex' _ = 0
  ctorCount :: proxy t -> Int
  ctorCount _ = 1

  generic' :: (Constraints' t c, GenericProfunctor p)
    => for c -> (forall s. c s => p s s) -> p (t x) (t x)

instance ADT' V1 where
  ctorCount _ = 0
  generic' _ _ = zero

instance (ADT' f, ADT' g) => ADT' (f :+: g) where
  ctorIndex' (L1 l) = ctorIndex' l
  ctorIndex' (R1 r) = ctorCount (Proxy :: Proxy f) + ctorIndex' r
  ctorCount _ = ctorCount (Proxy :: Proxy f) + ctorCount (Proxy :: Proxy g)
  generic' for f = plus (generic' for f) (generic' for f)

instance ADT' U1 where
  generic' _ _ = unit

instance (ADT' f, ADT' g) => ADT' (f :*: g) where
  generic' for f = mult (generic' for f) (generic' for f)

instance ADT' (K1 i v) where
  generic' _ = dimap unK1 K1

instance ADT' f => ADT' (M1 i t f) where
  ctorIndex' = ctorIndex' . unM1
  ctorCount _ = ctorCount (Proxy :: Proxy f)
  generic' for f = dimap unM1 M1 (generic' for f)


class (ADT' t) => ADTNonEmpty' (t :: * -> *) where
  nonEmpty' :: (Constraints' t c, GenericNonEmptyProfunctor p)
    => for c -> (forall s. c s => p s s) -> p (t x) (t x)

instance (ADTNonEmpty' f, ADTNonEmpty' g) => ADTNonEmpty' (f :+: g) where
  nonEmpty' for f = plus (nonEmpty' for f) (nonEmpty' for f)

instance ADTNonEmpty' U1 where
  nonEmpty' _ _ = unit

instance (ADTNonEmpty' f, ADTNonEmpty' g) => ADTNonEmpty' (f :*: g) where
  nonEmpty' for f = mult (nonEmpty' for f) (nonEmpty' for f)

instance ADTNonEmpty' (K1 i v) where
  nonEmpty' _ = dimap unK1 K1

instance ADTNonEmpty' f => ADTNonEmpty' (M1 i t f) where
  nonEmpty' for f = dimap unM1 M1 (nonEmpty' for f)


class (ADTNonEmpty' t) => ADTRecord' (t :: * -> *) where
  record' :: (Constraints' t c, GenericRecordProfunctor p)
    => for c -> (forall s. c s => p s s) -> p (t x) (t x)

instance ADTRecord' U1 where
  record' _ _ = unit

instance (ADTRecord' f, ADTRecord' g) => ADTRecord' (f :*: g) where
  record' for f = mult (record' for f) (record' for f)

instance ADTRecord' (K1 i v) where
  record' _ = dimap unK1 K1

instance ADTRecord' f => ADTRecord' (M1 i t f) where
  record' for f = dimap unM1 M1 (record' for f)


class Profunctor p => GenericRecordProfunctor p where
  unit :: p (U1 a) (U1 a)
  mult :: p (f a) (f' a) -> p (g a) (g' a) -> p ((f :*: g) a) ((f' :*: g') a)

class GenericRecordProfunctor p => GenericNonEmptyProfunctor p where
  plus :: p (f a) (f' a) -> p (g a) (g' a) -> p ((f :+: g) a) ((f' :+: g') a)

class GenericNonEmptyProfunctor p => GenericProfunctor p where
  zero :: p (V1 a) (V1 a)


instance GenericRecordProfunctor (->) where
  unit _ = U1
  mult f g (l :*: r) = f l :*: g r
instance GenericNonEmptyProfunctor (->) where
  plus f _ (L1 l) = L1 (f l)
  plus _ g (R1 l) = R1 (g l)
instance GenericProfunctor (->) where
  zero = id


instance GenericRecordProfunctor Tagged where
  unit = Tagged U1
  mult (Tagged l) (Tagged r) = Tagged $ l :*: r


instance Applicative f => GenericRecordProfunctor (Star f) where
  unit = Star pure
  mult (Star f) (Star g) = Star $ \(l :*: r) -> (:*:) <$> f l <*> g r
instance Applicative f => GenericNonEmptyProfunctor (Star f) where
  plus (Star f) (Star g) = Star $ \case
    L1 l -> L1 <$> f l
    R1 r -> R1 <$> g r
instance Applicative f => GenericProfunctor (Star f) where
  zero = Star pure


instance Functor f => GenericRecordProfunctor (Costar f) where
  unit = Costar $ const U1
  mult (Costar f) (Costar g) = Costar $ \lr -> f ((\(l :*: _) -> l) <$> lr) :*: g ((\(_ :*: r) -> r) <$> lr)


instance Applicative f => GenericRecordProfunctor (Joker f) where
  unit = Joker $ pure U1
  mult (Joker l) (Joker r) = Joker $ (:*:) <$> l <*> r
instance Alternative f => GenericNonEmptyProfunctor (Joker f) where
  plus (Joker l) (Joker r) = Joker $ L1 <$> l <|> R1 <$> r
instance Alternative f => GenericProfunctor (Joker f) where
  zero = Joker empty


instance Divisible f => GenericRecordProfunctor (Clown f) where
  unit = Clown conquer
  mult (Clown f) (Clown g) = Clown $ divide (\(l :*: r) -> (l, r)) f g
instance Decidable f => GenericNonEmptyProfunctor (Clown f) where
  plus (Clown f) (Clown g) = Clown $ choose h f g where
    h (L1 l) = Left l
    h (R1 r) = Right r
instance Decidable f => GenericProfunctor (Clown f) where
  zero = Clown $ lose (\v -> v `seq` undefined)


-- | All the above functions have been implemented using this single function,
-- using different `profunctor`s.
generic :: (ADT t, Constraints t c, GenericProfunctor p)
        => for c -> (forall s. c s => p s s) -> p t t
generic for f = dimap from to $ generic' for f

nonEmpty :: (ADTNonEmpty t, Constraints t c, GenericNonEmptyProfunctor p)
        => for c -> (forall s. c s => p s s) -> p t t
nonEmpty for f = dimap from to $ nonEmpty' for f

record :: (ADTRecord t, Constraints t c, GenericRecordProfunctor p)
        => for c -> (forall s. c s => p s s) -> p t t
record for f = dimap from to $ record' for f

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
type ADTRecord t = (Generic t, ADTRecord' (Rep t), 1 ~ CtorCount t)

-- | `ADTNonEmpty` is a constraint type synonym. An instance is an `ADT` with *at least* one constructor.
type ADTNonEmpty t = (Generic t, ADTNonEmpty' (Rep t), 1 <= CtorCount t)

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
