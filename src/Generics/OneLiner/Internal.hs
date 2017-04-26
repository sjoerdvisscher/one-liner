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
  , EmptyCase
  , PolyKinds
  , RankNTypes
  , LambdaCase
  , TypeFamilies
  , TypeOperators
  , ConstraintKinds
  , FlexibleContexts
  , FlexibleInstances
  , ScopedTypeVariables
  , UndecidableInstances
  , MultiParamTypeClasses
  #-}
module Generics.OneLiner.Internal where

import GHC.Generics
import GHC.Types (Constraint)
import Control.Applicative
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Bifunctor.Tannen
import Data.Functor.Contravariant.Divisible
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Profunctor
import Data.Proxy
import Data.Tagged


type family Constraints' (t :: * -> *) (c :: * -> Constraint) (c1 :: (* -> *) -> Constraint) :: Constraint
type instance Constraints' V1 c c1 = ()
type instance Constraints' U1 c c1 = ()
type instance Constraints' (f :+: g) c c1 = (Constraints' f c c1, Constraints' g c c1)
type instance Constraints' (f :*: g) c c1 = (Constraints' f c c1, Constraints' g c c1)
type instance Constraints' (f :.: g) c c1 = (c1 f, Constraints' g c c1)
type instance Constraints' Par1 c c1 = ()
type instance Constraints' (Rec1 f) c c1 = c1 f
type instance Constraints' (K1 i a) c c1 = c a
type instance Constraints' (M1 i t f) c c1 = Constraints' f c c1

type ADT' = ADT_ Identity Proxy ADTProfunctor
type ADTNonEmpty' = ADT_ Identity Proxy NonEmptyProfunctor
type ADTRecord' = ADT_ Identity Proxy RecordProfunctor

type ADT1' = ADT_ Identity Identity ADTProfunctor
type ADTNonEmpty1' = ADT_ Proxy Identity NonEmptyProfunctor
type ADTRecord1' = ADT_ Proxy Identity RecordProfunctor

type ADTProfunctor = GenericProfunctor ': NonEmptyProfunctor
type NonEmptyProfunctor = GenericNonEmptyProfunctor ': RecordProfunctor
type RecordProfunctor = '[GenericRecordProfunctor, Profunctor]

type family Satisfies (p :: * -> * -> *) (ks :: [(* -> * -> *) -> Constraint]) :: Constraint
type instance Satisfies p (k ': ks) = (k p, Satisfies p ks)
type instance Satisfies p '[] = ()

class (ks :: [(* -> * -> *) -> Constraint]) |- (k :: (* -> * -> *) -> Constraint) where
  (|-) :: Satisfies p ks => proxy0 ks -> proxy1 k -> (k p => p a b) -> p a b

instance {-# OVERLAPPABLE #-} ks |- k => (_k ': ks) |- k where
  (_ :: proxy0 (_k ': ks)) |- proxy1 = (Proxy :: Proxy ks) |- proxy1

instance (k ': _ks) |- k where
  _ |- _ = id

generic' :: forall t c p ks a b proxy0 for. (ADT_ Identity Proxy ks t, Constraints' t c AnyType, Satisfies p ks)
         => proxy0 ks
         -> for c
         -> (forall s. c s => p s s)
         -> p (t a) (t b)
generic' proxy0 for f = generic_ proxy0 (Proxy :: Proxy Identity) for (Identity f) (For :: For AnyType) Proxy Proxy

nonEmpty1' :: forall t c1 p ks a b proxy0 for. (ADT_ Proxy Identity ks t, Constraints' t AnyType c1, Satisfies p ks)
           => proxy0 ks
           -> for c1
           -> (forall s a b. c1 s => p a b -> p (s a) (s b))
           -> p a b
           -> p (t a) (t b)
nonEmpty1' proxy0 for f p = generic_ proxy0 (Proxy :: Proxy Proxy) (For :: For AnyType) Proxy for (Identity f) (Identity p)

generic1' :: forall t c1 p ks a b proxy0 for. (ADT_ Identity Identity ks t, Constraints' t AnyType c1, Satisfies p ks, ks |- GenericProfunctor)
          => proxy0 ks
          -> for c1
          -> (forall s a b. c1 s => p a b -> p (s a) (s b))
          -> p a b
          -> p (t a) (t b)
generic1' proxy0 for f p = (proxy0 |- (Proxy :: Proxy GenericProfunctor))
  (generic_ proxy0 (Proxy :: Proxy Identity) (For :: For AnyType) (Identity identity) for (Identity f) (Identity p))

class ADT_ nullary (unary :: * -> *) (ks :: [(* -> * -> *) -> Constraint]) (t :: * -> *) where
  generic_ :: (Constraints' t c c1, Satisfies p ks)
           => proxy0 ks
           -> proxy1 nullary
           -> for c
           -> (forall s. c s => nullary (p s s))
           -> for1 c1
           -> (forall s1 a b. c1 s1 => unary (p a b -> p (s1 a) (s1 b)))
           -> unary (p a b)
           -> p (t a) (t b)

instance ks |- GenericProfunctor => ADT_ nullary unary ks V1 where
  generic_ proxy0 _ _ _ _ _ _ = (proxy0 |- (Proxy :: Proxy GenericProfunctor)) zero

instance ks |- GenericRecordProfunctor => ADT_ nullary unary ks U1 where
  generic_ proxy0 _ _ _ _ _ _ = (proxy0 |- (Proxy :: Proxy GenericRecordProfunctor)) unit

instance (ks |- GenericNonEmptyProfunctor, ADT_ nullary unary ks f, ADT_ nullary unary ks g) => ADT_ nullary unary ks (f :+: g) where
  generic_ proxy0 proxy1 for f for1 f1 p1 = (proxy0 |- (Proxy :: Proxy GenericNonEmptyProfunctor))
    (plus (generic_ proxy0 proxy1 for f for1 f1 p1) (generic_ proxy0 proxy1 for f for1 f1 p1))

instance (ks |- GenericRecordProfunctor, ADT_ nullary unary ks f, ADT_ nullary unary ks g) => ADT_ nullary unary ks (f :*: g) where
  generic_ proxy0 proxy1 for f for1 f1 p1 = (proxy0 |- (Proxy :: Proxy GenericRecordProfunctor))
    (mult (generic_ proxy0 proxy1 for f for1 f1 p1) (generic_ proxy0 proxy1 for f for1 f1 p1))

instance ks |- Profunctor => ADT_ Identity unary ks (K1 i v) where
  generic_ proxy0 _ _ f _ _ _ = (proxy0 |- (Proxy :: Proxy Profunctor)) (dimap unK1 K1 (runIdentity f))

instance (ks |- Profunctor, ADT_ nullary unary ks f) => ADT_ nullary unary ks (M1 i c f) where
  generic_ proxy0 proxy1 for f for1 f1 p1 = (proxy0 |- (Proxy :: Proxy Profunctor))
    (dimap unM1 M1 (generic_ proxy0 proxy1 for f for1 f1 p1))

instance (ks |- Profunctor, ADT_ nullary Identity ks g) => ADT_ nullary Identity ks (f :.: g) where
  generic_ proxy0 proxy1 for f for1 f1 p1 = (proxy0 |- (Proxy :: Proxy Profunctor))
    (dimap unComp1 Comp1 $ runIdentity f1 (generic_ proxy0 proxy1 for f for1 f1 p1))

instance ks |- Profunctor => ADT_ nullary Identity ks Par1 where
  generic_ proxy0 _ _ _ _ _ p = (proxy0 |- (Proxy :: Proxy Profunctor))
    (dimap unPar1 Par1 (runIdentity p))

instance ks |- Profunctor => ADT_ nullary Identity ks (Rec1 f) where
  generic_ proxy0 _ _ _ _ f p = (proxy0 |- (Proxy :: Proxy Profunctor))
    (dimap unRec1 Rec1 (runIdentity (f <*> p)))

absurd :: V1 a -> b
absurd = \case {}

e1 :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
e1 f _ (L1 l) = f l
e1 _ f (R1 r) = f r

fst1 :: (f :*: g) a -> f a
fst1 (l :*: _) = l
snd1 :: (f :*: g) a -> g a
snd1 (_ :*: r) = r

-- | A generic function using a `GenericRecordProfunctor` works on any data type
-- with exactly one constructor, a.k.a. records,
-- with multiple fields (`mult`) or no fields (`unit`).
--
-- `GenericRecordProfunctor` is similar to `ProductProfuctor` from the
-- product-profunctor package, but using types from GHC.Generics.
class Profunctor p => GenericRecordProfunctor p where
  unit :: p (U1 a) (U1 a')
  mult :: p (f a) (f' a') -> p (g a) (g' a') -> p ((f :*: g) a) ((f' :*: g') a')

-- | A generic function using a `GenericNonEmptyProfunctor` works on any data
-- type with at least one constructor.
class GenericRecordProfunctor p => GenericNonEmptyProfunctor p where
  plus :: p (f a) (f' a') -> p (g a) (g' a') -> p ((f :+: g) a) ((f' :+: g') a')

-- | A generic function using a `GenericProfunctor` works on any
-- algebraic data type, including those with no constructors and constants.
class GenericNonEmptyProfunctor p => GenericProfunctor p where
  identity :: p a a
  zero :: p (V1 a) (V1 a')
  zero = lmap absurd identity

instance GenericRecordProfunctor (->) where
  unit _ = U1
  mult f g (l :*: r) = f l :*: g r
instance GenericNonEmptyProfunctor (->) where
  plus f g = e1 (L1 . f) (R1 . g)
instance GenericProfunctor (->) where
  zero = absurd
  identity = id

instance GenericRecordProfunctor Tagged where
  unit = Tagged U1
  mult (Tagged l) (Tagged r) = Tagged $ l :*: r

instance Applicative f => GenericRecordProfunctor (Star f) where
  unit = Star $ \_ -> pure U1
  mult (Star f) (Star g) = Star $ \(l :*: r) -> (:*:) <$> f l <*> g r
instance Applicative f => GenericNonEmptyProfunctor (Star f) where
  plus (Star f) (Star g) = Star $ e1 (fmap L1 . f) (fmap R1 . g)
instance Applicative f => GenericProfunctor (Star f) where
  zero = Star absurd
  identity = Star pure

instance Functor f => GenericRecordProfunctor (Costar f) where
  unit = Costar $ const U1
  mult (Costar f) (Costar g) = Costar $ \lr -> f (fst1 <$> lr) :*: g (snd1 <$> lr)

instance (Functor f, Applicative g, GenericRecordProfunctor p) => GenericRecordProfunctor (Biff p f g) where
  unit = Biff $ dimap (const U1) pure unit
  mult (Biff f) (Biff g) = Biff $ dimap
    (liftA2 (:*:) (Compose . fmap fst1) (Compose . fmap snd1))
    (\(Compose l :*: Compose r) -> liftA2 (:*:) l r)
    (mult (dimap getCompose Compose f) (dimap getCompose Compose g))

instance Applicative f => GenericRecordProfunctor (Joker f) where
  unit = Joker $ pure U1
  mult (Joker l) (Joker r) = Joker $ (:*:) <$> l <*> r
instance Alternative f => GenericNonEmptyProfunctor (Joker f) where
  plus (Joker l) (Joker r) = Joker $ L1 <$> l <|> R1 <$> r
instance Alternative f => GenericProfunctor (Joker f) where
  zero = Joker empty
  identity = Joker empty

instance Divisible f => GenericRecordProfunctor (Clown f) where
  unit = Clown conquer
  mult (Clown f) (Clown g) = Clown $ divide (\(l :*: r) -> (l, r)) f g
instance Decidable f => GenericNonEmptyProfunctor (Clown f) where
  plus (Clown f) (Clown g) = Clown $ choose (e1 Left Right) f g where
instance Decidable f => GenericProfunctor (Clown f) where
  zero = Clown $ lose absurd
  identity = Clown conquer

instance (GenericRecordProfunctor p, GenericRecordProfunctor q) => GenericRecordProfunctor (Product p q) where
  unit = Pair unit unit
  mult (Pair l1 r1) (Pair l2 r2) = Pair (mult l1 l2) (mult r1 r2)
instance (GenericNonEmptyProfunctor p, GenericNonEmptyProfunctor q) => GenericNonEmptyProfunctor (Product p q) where
  plus (Pair l1 r1) (Pair l2 r2) = Pair (plus l1 l2) (plus r1 r2)
instance (GenericProfunctor p, GenericProfunctor q) => GenericProfunctor (Product p q) where
  zero = Pair zero zero
  identity = Pair identity identity

instance (Applicative f, GenericRecordProfunctor p) => GenericRecordProfunctor (Tannen f p) where
  unit = Tannen (pure unit)
  mult (Tannen l) (Tannen r) = Tannen $ liftA2 mult l r
instance (Applicative f, GenericNonEmptyProfunctor p) => GenericNonEmptyProfunctor (Tannen f p) where
  plus (Tannen l) (Tannen r) = Tannen $ liftA2 plus l r
instance (Applicative f, GenericProfunctor p) => GenericProfunctor (Tannen f p) where
  zero = Tannen (pure zero)
  identity = Tannen (pure identity)

data Ctor a b = Ctor { index :: a -> Int, count :: Int }
instance Profunctor Ctor where
  dimap l _ (Ctor i c) = Ctor (i . l) c
instance GenericRecordProfunctor Ctor where
  unit = Ctor (const 0) 1
  mult _ _ = Ctor (const 0) 1
instance GenericNonEmptyProfunctor Ctor where
  plus l r = Ctor (e1 (index l) ((count l + ) . index r)) (count l + count r)
instance GenericProfunctor Ctor where
  zero = Ctor (const 0) 0
  identity = Ctor (const 0) 1

record :: (ADTRecord t, Constraints t c, GenericRecordProfunctor p)
       => for c -> (forall s. c s => p s s) -> p t t
record for f = dimap from to $ generic' (Proxy :: Proxy RecordProfunctor) for f

record1 :: (ADTRecord1 t, Constraints1 t c, GenericRecordProfunctor p)
        => for c -> (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
record1 for f p = dimap from1 to1 $ nonEmpty1' (Proxy :: Proxy RecordProfunctor) for f p

nonEmpty :: (ADTNonEmpty t, Constraints t c, GenericNonEmptyProfunctor p)
         => for c -> (forall s. c s => p s s) -> p t t
nonEmpty for f = dimap from to $ generic' (Proxy :: Proxy NonEmptyProfunctor) for f

nonEmpty1 :: (ADTNonEmpty1 t, Constraints1 t c, GenericNonEmptyProfunctor p)
          => for c -> (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
nonEmpty1 for f p = dimap from1 to1 $ nonEmpty1' (Proxy :: Proxy NonEmptyProfunctor) for f p

generic :: (ADT t, Constraints t c, GenericProfunctor p)
        => for c -> (forall s. c s => p s s) -> p t t
generic for f = dimap from to $ generic' (Proxy :: Proxy ADTProfunctor) for f

generic1 :: (ADT1 t, Constraints1 t c, GenericProfunctor p)
         => for c -> (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
generic1 for f p = dimap from1 to1 $ generic1' (Proxy :: Proxy ADTProfunctor) for f p

-- | `Constraints` is a constraint type synonym, containing the constraint
-- requirements for an instance for `t` of class `c`.
-- It requires an instance of class `c` for each component of `t`.
type Constraints t c = (Constraints' (Rep t) c AnyType)

type Constraints1 t c = Constraints' (Rep1 t) AnyType c

-- | `ADTRecord` is a constraint type synonym. An instance is an `ADT` with *exactly* one constructor.
type ADTRecord t = (Generic t, ADTRecord' (Rep t), Constraints t AnyType)

type ADTRecord1 t = (Generic1 t, ADTRecord1' (Rep1 t), Constraints1 t AnyType)

-- | `ADTNonEmpty` is a constraint type synonym. An instance is an `ADT` with *at least* one constructor.
type ADTNonEmpty t = (Generic t, ADTNonEmpty' (Rep t), Constraints t AnyType)

type ADTNonEmpty1 t = (Generic1 t, ADTNonEmpty1' (Rep1 t), Constraints1 t AnyType)

-- | `ADT` is a constraint type synonym. The `Generic` instance can be derived,
-- and any generic representation will be an instance of `ADT'` and `AnyType`.
type ADT t = (Generic t, ADT' (Rep t), Constraints t AnyType)

type ADT1 t = (Generic1 t, ADT1' (Rep1 t), Constraints1 t AnyType)

-- | Tell the compiler which class we want to use in the traversal. Should be used like this:
--
-- > (For :: For Show)
--
-- Where @Show@ can be any class.
data For (c :: k -> Constraint) = For

-- | Get the index in the lists returned by `create` and `createA` of the constructor of the given value.
--
-- For example, this is the implementation of `put` that generates the binary data that
-- the above implentation of `get` expects:
--
-- @
-- `put` t = `putWord8` (`toEnum` (`ctorIndex` t)) `<>` `gfoldMap` (`For` :: `For` `Binary`) `put` t
-- @
ctorIndex :: ADT t => t -> Int
ctorIndex = index $ generic (For :: For AnyType) (Ctor (const 0) 1)

ctorIndex1 :: ADT1 t => t a -> Int
ctorIndex1 = index $ generic1 (For :: For AnyType) (const $ Ctor (const 0) 1) (Ctor (const 0) 1)

-- | Any type is instance of `AnyType`, you can use it with @For :: For AnyType@
-- if you don't actually need a class constraint.
class AnyType (a :: k)
instance AnyType (a :: k)

-- | The result type of a curried function.
--
-- If @r@ is not a function type (i.e., does not unify with `_ -> _`):
--
-- @
-- `Result` (a -> r) ~ r
-- `Result` (a -> b -> r) ~ r
-- `Result` (a -> b -> c -> r) ~ r
-- @
type family Result t where
  Result (a -> b) = Result b
  Result r = r

-- | Automatically apply a lifted function to a polymorphic argument as
-- many times as possible.
--
-- A constraint `FunConstraint t c` is equivalent to the conjunction of
-- constraints `c s` for every argument type of `t`.
--
-- If @r@ is not a function type:
--
-- @
-- c a :- FunConstraints (a -> r) c
-- (c a, c b) :- FunConstraints (a -> b -> r) c
-- (c a, c b, c d) :- FunConstraints (a -> b -> d -> r) c
-- @
class FunConstraints t c where
  autoApply :: Applicative f => for c -> (forall s. c s => f s) -> f t -> f (Result t)

instance {-# OVERLAPPING #-} (c a, FunConstraints b c) => FunConstraints (a -> b) c where
  autoApply for run f = autoApply for run (f <*> run)

instance Result r ~ r => FunConstraints r c where
  autoApply _for _run r = r
