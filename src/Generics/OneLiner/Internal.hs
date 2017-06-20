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
  , TypeApplications
  , FlexibleContexts
  , FlexibleInstances
  , AllowAmbiguousTypes
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

type ADT1' t = (ADT_ Identity Identity ADTProfunctor t, ADT_ Proxy Identity ADTProfunctor t)
type ADTNonEmpty1' t = (ADT_ Identity Identity NonEmptyProfunctor t, ADT_ Proxy Identity NonEmptyProfunctor t)
type ADTRecord1' t = (ADT_ Identity Identity RecordProfunctor t, ADT_ Proxy Identity RecordProfunctor t)

type ADTProfunctor = GenericEmptyProfunctor ': NonEmptyProfunctor
type NonEmptyProfunctor = GenericSumProfunctor ': RecordProfunctor
type RecordProfunctor = '[GenericProductProfunctor, GenericUnitProfunctor, Profunctor]

type family Satisfies (p :: * -> * -> *) (ks :: [(* -> * -> *) -> Constraint]) :: Constraint
type instance Satisfies p (k ': ks) = (k p, Satisfies p ks)
type instance Satisfies p '[] = ()

class (ks :: [(* -> * -> *) -> Constraint]) |- (k :: (* -> * -> *) -> Constraint) where
  (|-) :: Satisfies p ks => proxy0 ks -> proxy1 k -> (k p => p a b) -> p a b

instance {-# OVERLAPPABLE #-} ks |- k => (_k ': ks) |- k where
  (_ :: proxy0 (_k ': ks)) |- proxy1 = (Proxy :: Proxy ks) |- proxy1
  {-# INLINE (|-) #-}

instance (k ': _ks) |- k where
  _ |- _ = id
  {-# INLINE (|-) #-}

generic' :: forall t c p ks a b proxy0 for. (ADT_ Identity Proxy ks t, Constraints' t c AnyType, Satisfies p ks)
         => proxy0 ks
         -> for c
         -> (forall s. c s => p s s)
         -> p (t a) (t b)
generic' proxy0 for f = generic_ proxy0 (Proxy :: Proxy Identity) for (Identity f) (Proxy :: Proxy AnyType) Proxy Proxy
{-# INLINE generic' #-}

generic1' :: forall t c1 p ks a b proxy0 for. (ADT_ Proxy Identity ks t, Constraints' t AnyType c1, Satisfies p ks)
           => proxy0 ks
           -> for c1
           -> (forall s d e. c1 s => p d e -> p (s d) (s e))
           -> p a b
           -> p (t a) (t b)
generic1' proxy0 for f p = generic_ proxy0 (Proxy :: Proxy Proxy) (Proxy :: Proxy AnyType) Proxy for (Identity f) (Identity p)
{-# INLINE generic1' #-}

generic01' :: forall t c0 c1 p ks a b proxy0 for for1. (ADT_ Identity Identity ks t, Constraints' t c0 c1, Satisfies p ks)
          => proxy0 ks
          -> for c0
          -> (forall s. c0 s => p s s)
          -> for1 c1
          -> (forall s d e. c1 s => p d e -> p (s d) (s e))
          -> p a b
          -> p (t a) (t b)
generic01' proxy0 for0 k for1 f p = generic_ proxy0 (Proxy :: Proxy Identity) for0 (Identity k) for1 (Identity f) (Identity p)
{-# INLINE generic01' #-}

class ADT_ (nullary :: * -> *) (unary :: * -> *) (ks :: [(* -> * -> *) -> Constraint]) (t :: * -> *) where
  generic_ :: (Constraints' t c c1, Satisfies p ks)
           => proxy0 ks
           -> proxy1 nullary
           -> for c
           -> (forall s. c s => nullary (p s s))
           -> for1 c1
           -> (forall s1 d e. c1 s1 => unary (p d e -> p (s1 d) (s1 e)))
           -> unary (p a b)
           -> p (t a) (t b)

instance ks |- GenericEmptyProfunctor => ADT_ nullary unary ks V1 where
  generic_ proxy0 _ _ _ _ _ _ = (proxy0 |- (Proxy :: Proxy GenericEmptyProfunctor)) zero
  {-# INLINE generic_ #-}

instance ks |- GenericUnitProfunctor => ADT_ nullary unary ks U1 where
  generic_ proxy0 _ _ _ _ _ _ = (proxy0 |- (Proxy :: Proxy GenericUnitProfunctor)) unit
  {-# INLINE generic_ #-}

instance (ks |- GenericSumProfunctor, ADT_ nullary unary ks f, ADT_ nullary unary ks g) => ADT_ nullary unary ks (f :+: g) where
  generic_ proxy0 proxy1 for f for1 f1 p1 = (proxy0 |- (Proxy :: Proxy GenericSumProfunctor))
    (plus (generic_ proxy0 proxy1 for f for1 f1 p1) (generic_ proxy0 proxy1 for f for1 f1 p1))
  {-# INLINE generic_ #-}

instance (ks |- GenericProductProfunctor, ADT_ nullary unary ks f, ADT_ nullary unary ks g) => ADT_ nullary unary ks (f :*: g) where
  generic_ proxy0 proxy1 for f for1 f1 p1 = (proxy0 |- (Proxy :: Proxy GenericProductProfunctor))
    (mult (generic_ proxy0 proxy1 for f for1 f1 p1) (generic_ proxy0 proxy1 for f for1 f1 p1))
  {-# INLINE generic_ #-}

instance ks |- Profunctor => ADT_ Identity unary ks (K1 i v) where
  generic_ proxy0 _ _ f _ _ _ = (proxy0 |- (Proxy :: Proxy Profunctor)) (dimap unK1 K1 (runIdentity f))
  {-# INLINE generic_ #-}

instance ks |- GenericEmptyProfunctor => ADT_ Proxy unary ks (K1 i v) where
  generic_ proxy0 _ _ _ _ _ _ = (proxy0 |- (Proxy :: Proxy GenericEmptyProfunctor)) (dimap unK1 K1 identity)
  {-# INLINE generic_ #-}

instance (ks |- Profunctor, ADT_ nullary unary ks f) => ADT_ nullary unary ks (M1 i c f) where
  generic_ proxy0 proxy1 for f for1 f1 p1 = (proxy0 |- (Proxy :: Proxy Profunctor))
    (dimap unM1 M1 (generic_ proxy0 proxy1 for f for1 f1 p1))
  {-# INLINE generic_ #-}

instance (ks |- Profunctor, ADT_ nullary Identity ks g) => ADT_ nullary Identity ks (f :.: g) where
  generic_ proxy0 proxy1 for f for1 f1 p1 = (proxy0 |- (Proxy :: Proxy Profunctor))
    (dimap unComp1 Comp1 $ runIdentity f1 (generic_ proxy0 proxy1 for f for1 f1 p1))
  {-# INLINE generic_ #-}

instance ks |- Profunctor => ADT_ nullary Identity ks Par1 where
  generic_ proxy0 _ _ _ _ _ p = (proxy0 |- (Proxy :: Proxy Profunctor))
    (dimap unPar1 Par1 (runIdentity p))
  {-# INLINE generic_ #-}

instance ks |- Profunctor => ADT_ nullary Identity ks (Rec1 f) where
  generic_ proxy0 _ _ _ _ f p = (proxy0 |- (Proxy :: Proxy Profunctor))
    (dimap unRec1 Rec1 (runIdentity (f <*> p)))
  {-# INLINE generic_ #-}

absurd :: V1 a -> b
absurd = \case {}
{-# INLINE absurd #-}

e1 :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
e1 f _ (L1 l) = f l
e1 _ f (R1 r) = f r
{-# INLINE e1 #-}

fst1 :: (f :*: g) a -> f a
fst1 (l :*: _) = l
{-# INLINE fst1 #-}
snd1 :: (f :*: g) a -> g a
snd1 (_ :*: r) = r
{-# INLINE snd1 #-}

class Profunctor p => GenericUnitProfunctor p where
  unit :: p (U1 a) (U1 a')

class Profunctor p => GenericProductProfunctor p where
  mult :: p (f a) (f' a') -> p (g a) (g' a') -> p ((f :*: g) a) ((f' :*: g') a')

class Profunctor p => GenericSumProfunctor p where
  plus :: p (f a) (f' a') -> p (g a) (g' a') -> p ((f :+: g) a) ((f' :+: g') a')

class Profunctor p => GenericEmptyProfunctor p where
  identity :: p a a
  zero :: p (V1 a) (V1 a')

-- | A generic function using a `GenericRecordProfunctor` works on any data type
-- with exactly one constructor, a.k.a. records,
-- with multiple fields (`mult`) or no fields (`unit`).
--
-- `GenericRecordProfunctor` is similar to `ProductProfuctor` from the
-- product-profunctor package, but using types from GHC.Generics.
class (Profunctor p, GenericUnitProfunctor p, GenericProductProfunctor p) => GenericRecordProfunctor p
instance (Profunctor p, GenericUnitProfunctor p, GenericProductProfunctor p) => GenericRecordProfunctor p

-- | A generic function using a `GenericNonEmptyProfunctor` works on any data
-- type with at least one constructor.
class (GenericRecordProfunctor p, GenericSumProfunctor p) => GenericNonEmptyProfunctor p where
instance (GenericRecordProfunctor p, GenericSumProfunctor p) => GenericNonEmptyProfunctor p where

-- | A generic function using a `GenericProfunctor` works on any
-- algebraic data type, including those with no constructors and constants.
class (GenericNonEmptyProfunctor p, GenericEmptyProfunctor p) => GenericProfunctor p where
instance (GenericNonEmptyProfunctor p, GenericEmptyProfunctor p) => GenericProfunctor p where

instance GenericUnitProfunctor (->) where
  unit _ = U1
  {-# INLINE unit #-}
instance GenericProductProfunctor (->) where
  mult f g (l :*: r) = f l :*: g r
  {-# INLINE mult #-}
instance GenericSumProfunctor (->) where
  plus f g = e1 (L1 . f) (R1 . g)
  {-# INLINE plus #-}
instance GenericEmptyProfunctor (->) where
  zero = absurd
  {-# INLINE zero #-}
  identity = id
  {-# INLINE identity #-}

instance GenericUnitProfunctor Tagged where
  unit = Tagged U1
  {-# INLINE unit #-}
instance GenericProductProfunctor Tagged where
  mult (Tagged l) (Tagged r) = Tagged $ l :*: r
  {-# INLINE mult #-}

instance Applicative f => GenericUnitProfunctor (Star f) where
  unit = Star $ \_ -> pure U1
  {-# INLINE unit #-}
instance Applicative f => GenericProductProfunctor (Star f) where
  mult (Star f) (Star g) = Star $ \(l :*: r) -> (:*:) <$> f l <*> g r
  {-# INLINE mult #-}
instance Applicative f => GenericSumProfunctor (Star f) where
  plus (Star f) (Star g) = Star $ e1 (fmap L1 . f) (fmap R1 . g)
  {-# INLINE plus #-}
instance Applicative f => GenericEmptyProfunctor (Star f) where
  zero = Star absurd
  {-# INLINE zero #-}
  identity = Star pure
  {-# INLINE identity #-}

instance Functor f => GenericUnitProfunctor (Costar f) where
  unit = Costar $ const U1
  {-# INLINE unit #-}
instance Functor f => GenericProductProfunctor (Costar f) where
  mult (Costar f) (Costar g) = Costar $ \lr -> f (fst1 <$> lr) :*: g (snd1 <$> lr)
  {-# INLINE mult #-}

instance (Functor f, Applicative g, Profunctor p, GenericUnitProfunctor p) => GenericUnitProfunctor (Biff p f g) where
  unit = Biff $ dimap (const U1) pure unit
  {-# INLINE unit #-}
instance (Functor f, Applicative g, Profunctor p, GenericProductProfunctor p) => GenericProductProfunctor (Biff p f g) where
  mult (Biff f) (Biff g) = Biff $ dimap
    (liftA2 (:*:) (Compose . fmap fst1) (Compose . fmap snd1))
    (\(Compose l :*: Compose r) -> liftA2 (:*:) l r)
    (mult (dimap getCompose Compose f) (dimap getCompose Compose g))
  {-# INLINE mult #-}

instance Applicative f => GenericUnitProfunctor (Joker f) where
  unit = Joker $ pure U1
  {-# INLINE unit #-}
instance Applicative f => GenericProductProfunctor (Joker f) where
  mult (Joker l) (Joker r) = Joker $ (:*:) <$> l <*> r
  {-# INLINE mult #-}
instance Alternative f => GenericSumProfunctor (Joker f) where
  plus (Joker l) (Joker r) = Joker $ L1 <$> l <|> R1 <$> r
  {-# INLINE plus #-}
instance Alternative f => GenericEmptyProfunctor (Joker f) where
  zero = Joker empty
  {-# INLINE zero #-}
  identity = Joker empty
  {-# INLINE identity #-}

instance Divisible f => GenericUnitProfunctor (Clown f) where
  unit = Clown conquer
  {-# INLINE unit #-}
instance Divisible f => GenericProductProfunctor (Clown f) where
  mult (Clown f) (Clown g) = Clown $ divide (\(l :*: r) -> (l, r)) f g
  {-# INLINE mult #-}
instance Decidable f => GenericSumProfunctor (Clown f) where
  plus (Clown f) (Clown g) = Clown $ choose (e1 Left Right) f g
  {-# INLINE plus #-}
instance Decidable f => GenericEmptyProfunctor (Clown f) where
  zero = Clown $ lose absurd
  {-# INLINE zero #-}
  identity = Clown conquer
  {-# INLINE identity #-}

instance (GenericUnitProfunctor p, GenericUnitProfunctor q) => GenericUnitProfunctor (Product p q) where
  unit = Pair unit unit
  {-# INLINE unit #-}
instance (GenericProductProfunctor p, GenericProductProfunctor q) => GenericProductProfunctor (Product p q) where
  mult (Pair l1 r1) (Pair l2 r2) = Pair (mult l1 l2) (mult r1 r2)
  {-# INLINE mult #-}
instance (GenericSumProfunctor p, GenericSumProfunctor q) => GenericSumProfunctor (Product p q) where
  plus (Pair l1 r1) (Pair l2 r2) = Pair (plus l1 l2) (plus r1 r2)
  {-# INLINE plus #-}
instance (GenericEmptyProfunctor p, GenericEmptyProfunctor q) => GenericEmptyProfunctor (Product p q) where
  zero = Pair zero zero
  {-# INLINE zero #-}
  identity = Pair identity identity
  {-# INLINE identity #-}

instance (Applicative f, GenericUnitProfunctor p) => GenericUnitProfunctor (Tannen f p) where
  unit = Tannen (pure unit)
  {-# INLINE unit #-}
instance (Applicative f, GenericProductProfunctor p) => GenericProductProfunctor (Tannen f p) where
  mult (Tannen l) (Tannen r) = Tannen $ liftA2 mult l r
  {-# INLINE mult #-}
instance (Applicative f, GenericSumProfunctor p) => GenericSumProfunctor (Tannen f p) where
  plus (Tannen l) (Tannen r) = Tannen $ liftA2 plus l r
  {-# INLINE plus #-}
instance (Applicative f, GenericEmptyProfunctor p) => GenericEmptyProfunctor (Tannen f p) where
  zero = Tannen (pure zero)
  {-# INLINE zero #-}
  identity = Tannen (pure identity)
  {-# INLINE identity #-}

data Ctor a b = Ctor { index :: a -> Int, count :: Int }
instance Profunctor Ctor where
  dimap l _ (Ctor i c) = Ctor (i . l) c
  {-# INLINE dimap #-}
instance GenericUnitProfunctor Ctor where
  unit = Ctor (const 0) 1
  {-# INLINE unit #-}
instance GenericProductProfunctor Ctor where
  mult _ _ = Ctor (const 0) 1
  {-# INLINE mult #-}
instance GenericSumProfunctor Ctor where
  plus l r = Ctor (e1 (index l) ((count l + ) . index r)) (count l + count r)
  {-# INLINE plus #-}
instance GenericEmptyProfunctor Ctor where
  zero = Ctor (const 0) 0
  {-# INLINE zero #-}
  identity = Ctor (const 0) 1
  {-# INLINE identity #-}

record :: forall c p t. (ADTRecord t, Constraints t c, GenericRecordProfunctor p)
       => (forall s. c s => p s s) -> p t t
record f = dimap from to $ generic' (Proxy :: Proxy RecordProfunctor) (Proxy :: Proxy c) f
{-# INLINE record #-}

record1 :: forall c p t a b. (ADTRecord1 t, Constraints1 t c, GenericRecordProfunctor p)
        => (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
record1 f p = dimap from1 to1 $ generic1' (Proxy :: Proxy RecordProfunctor) (Proxy :: Proxy c) f p
{-# INLINE record1 #-}

record01 :: forall c0 c1 p t a b. (ADTRecord1 t, Constraints01 t c0 c1, GenericRecordProfunctor p)
         => (forall s. c0 s => p s s) -> (forall d e s. c1 s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
record01 k f p = dimap from1 to1 $ generic01' (Proxy :: Proxy RecordProfunctor) (Proxy :: Proxy c0) k (Proxy :: Proxy c1) f p
{-# INLINE record01 #-}

nonEmpty :: forall c p t. (ADTNonEmpty t, Constraints t c, GenericNonEmptyProfunctor p)
         => (forall s. c s => p s s) -> p t t
nonEmpty f = dimap from to $ generic' (Proxy :: Proxy NonEmptyProfunctor) (Proxy :: Proxy c) f
{-# INLINE nonEmpty #-}

nonEmpty1 :: forall c p t a b. (ADTNonEmpty1 t, Constraints1 t c, GenericNonEmptyProfunctor p)
          => (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
nonEmpty1 f p = dimap from1 to1 $ generic1' (Proxy :: Proxy NonEmptyProfunctor) (Proxy :: Proxy c) f p
{-# INLINE nonEmpty1 #-}

nonEmpty01 :: forall c0 c1 p t a b. (ADTNonEmpty1 t, Constraints01 t c0 c1, GenericNonEmptyProfunctor p)
           => (forall s. c0 s => p s s) -> (forall d e s. c1 s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
nonEmpty01 k f p = dimap from1 to1 $ generic01' (Proxy :: Proxy NonEmptyProfunctor) (Proxy :: Proxy c0) k (Proxy :: Proxy c1) f p
{-# INLINE nonEmpty01 #-}

generic :: forall c p t. (ADT t, Constraints t c, GenericProfunctor p)
        => (forall s. c s => p s s) -> p t t
generic f = dimap from to $ generic' (Proxy :: Proxy ADTProfunctor) (Proxy :: Proxy c) f
{-# INLINE generic #-}

generic1 :: forall c p t a b. (ADT1 t, Constraints1 t c, GenericProfunctor p)
         => (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
generic1 f p = dimap from1 to1 $ generic1' (Proxy :: Proxy ADTProfunctor) (Proxy :: Proxy c) f p
{-# INLINE generic1 #-}

generic01 :: forall c0 c1 p t a b. (ADT1 t, Constraints01 t c0 c1, GenericProfunctor p)
          => (forall s. c0 s => p s s) -> (forall d e s. c1 s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
generic01 k f p = dimap from1 to1 $ generic01' (Proxy :: Proxy ADTProfunctor) (Proxy :: Proxy c0) k (Proxy :: Proxy c1) f p
{-# INLINE generic01 #-}

-- | `Constraints` is a constraint type synonym, containing the constraint
-- requirements for an instance for `t` of class `c`.
-- It requires an instance of class `c` for each component of `t`.
type Constraints t c = Constraints' (Rep t) c AnyType

type Constraints1 t c = Constraints' (Rep1 t) AnyType c

type Constraints01 t c0 c1 = Constraints' (Rep1 t) c0 c1

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

-- | Get the index in the lists returned by `create` and `createA` of the constructor of the given value.
--
-- For example, this is the implementation of `put` that generates the binary data that
-- the above implentation of `get` expects:
--
-- @
-- `put` t = `putWord8` (`toEnum` (`ctorIndex` t)) `<>` `gfoldMap` \@`Binary` `put` t
-- @
ctorIndex :: ADT t => t -> Int
ctorIndex = index $ generic @AnyType (Ctor (const 0) 1)
{-# INLINE ctorIndex #-}

ctorIndex1 :: ADT1 t => t a -> Int
ctorIndex1 = index $ generic1 @AnyType (const $ Ctor (const 0) 1) (Ctor (const 0) 1)
{-# INLINE ctorIndex1 #-}

-- | Any type is instance of `AnyType`, you can use it with @\@`AnyType`@
-- if you don't actually need a class constraint.
class AnyType (a :: k)
instance AnyType (a :: k)

-- | The result type of a curried function.
--
-- If @r@ is not a function type (i.e., does not unify with `_ -> _`):
--
-- @
-- `FunResult` (a -> r) ~ r
-- `FunResult` (a -> b -> r) ~ r
-- `FunResult` (a -> b -> c -> r) ~ r
-- @
type family FunResult t where
  FunResult (a -> b) = FunResult b
  FunResult r = r

-- | Automatically apply a lifted function to a polymorphic argument as
-- many times as possible.
--
-- A constraint `FunConstraint c t` is equivalent to the conjunction of
-- constraints `c s` for every argument type of `t`.
--
-- If @r@ is not a function type:
--
-- @
-- c a :- FunConstraints c (a -> r)
-- (c a, c b) :- FunConstraints c (a -> b -> r)
-- (c a, c b, c d) :- FunConstraints c (a -> b -> d -> r)
-- @
class FunConstraints c t where
  autoApply :: Applicative f => (forall s. c s => f s) -> f t -> f (FunResult t)

instance {-# OVERLAPPING #-} (c a, FunConstraints c b) => FunConstraints c (a -> b) where
  autoApply run f = autoApply @c run (f <*> run)
  {-# INLINE autoApply #-}

instance FunResult r ~ r => FunConstraints c r where
  autoApply _run r = r
  {-# INLINE autoApply #-}
