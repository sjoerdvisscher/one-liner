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
  , PolyKinds
  , RankNTypes
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
import Data.Profunctor
import Data.Proxy
import Data.Functor.Identity

import Generics.OneLiner.Classes

type family Constraints' (t :: * -> *) (t' :: * -> *) (c :: * -> * -> Constraint) (c1 :: (* -> *) -> (* -> *) -> Constraint) :: Constraint
type instance Constraints' V1 V1 c c1 = ()
type instance Constraints' U1 U1 c c1 = ()
type instance Constraints' (f :+: g) (f' :+: g') c c1 = (Constraints' f f' c c1, Constraints' g g' c c1)
type instance Constraints' (f :*: g) (f' :*: g') c c1 = (Constraints' f f' c c1, Constraints' g g' c c1)
type instance Constraints' (f :.: g) (f' :.: g') c c1 = (c1 f f', Constraints' g g' c c1)
type instance Constraints' Par1 Par1 c c1 = ()
type instance Constraints' (Rec1 f) (Rec1 g) c c1 = c1 f g
type instance Constraints' (K1 i a) (K1 i' b) c c1 = c a b
type instance Constraints' (M1 i t f) (M1 i' t' f') c c1 = Constraints' f f' c c1

type ADT' = ADT_ Identity Proxy ADTProfunctor
type ADTNonEmpty' = ADT_ Identity Proxy NonEmptyProfunctor
type ADTRecord' = ADT_ Identity Proxy RecordProfunctor

type ADT1' t t' = (ADT_ Identity Identity ADTProfunctor t t', ADT_ Proxy Identity ADTProfunctor t t')
type ADTNonEmpty1' t t' = (ADT_ Identity Identity NonEmptyProfunctor t t', ADT_ Proxy Identity NonEmptyProfunctor t t')
type ADTRecord1' t t' = (ADT_ Identity Identity RecordProfunctor t t', ADT_ Proxy Identity RecordProfunctor t t')

type ADTProfunctor = GenericEmptyProfunctor ': NonEmptyProfunctor
type NonEmptyProfunctor = GenericSumProfunctor ': RecordProfunctor
type RecordProfunctor = '[GenericProductProfunctor, GenericUnitProfunctor, Profunctor]

type family Satisfies (p :: * -> * -> *) (ks :: [(* -> * -> *) -> Constraint]) :: Constraint
type instance Satisfies p (k ': ks) = (k p, Satisfies p ks)
type instance Satisfies p '[] = ()

class (ks :: [(* -> * -> *) -> Constraint]) |- (k :: (* -> * -> *) -> Constraint) where
  implies :: Satisfies p ks => (k p => p a b) -> p a b

instance {-# OVERLAPPABLE #-} ks |- k => (_k ': ks) |- k where
  implies = implies @ks @k
  {-# INLINE implies #-}

instance (k ': _ks) |- k where
  implies = id
  {-# INLINE implies #-}

generic' :: forall ks c p t t' a b. (ADT_ Identity Proxy ks t t', Constraints' t t' c AnyType, Satisfies p ks)
         => (forall s s'. c s s' => p s s')
         -> p (t a) (t' b)
generic' f = generic_ @Identity @Proxy @ks (Proxy @c) (Identity f) (Proxy @AnyType) Proxy Proxy
{-# INLINE generic' #-}

generic1' :: forall ks c1 p t t' a b. (ADT_ Proxy Identity ks t t', Constraints' t t' AnyType c1, Satisfies p ks)
           => (forall s s' d e. c1 s s' => p d e -> p (s d) (s' e))
           -> p a b
           -> p (t a) (t' b)
generic1' f p = generic_ @Proxy @Identity @ks (Proxy @AnyType) Proxy (Proxy @c1) (Identity f) (Identity p)
{-# INLINE generic1' #-}

generic01' :: forall ks c0 c1 p t t' a b. (ADT_ Identity Identity ks t t', Constraints' t t' c0 c1, Satisfies p ks)
          => (forall s s'. c0 s s' => p s s')
          -> (forall s s' d e. c1 s s' => p d e -> p (s d) (s' e))
          -> p a b
          -> p (t a) (t' b)
generic01' k f p = generic_ @Identity @Identity @ks (Proxy @c0) (Identity k) (Proxy @c1) (Identity f) (Identity p)
{-# INLINE generic01' #-}

class ADT_ (nullary :: * -> *) (unary :: * -> *) (ks :: [(* -> * -> *) -> Constraint]) (t :: * -> *) (t' :: * -> *) where
  generic_ :: forall c c1 p a b. (Constraints' t t' c c1, Satisfies p ks)
           => Proxy c
           -> (forall s s'. c s s' => nullary (p s s'))
           -> Proxy c1
           -> (forall r1 s1 d e. c1 r1 s1 => unary (p d e -> p (r1 d) (s1 e)))
           -> unary (p a b)
           -> p (t a) (t' b)

instance ks |- GenericEmptyProfunctor => ADT_ nullary unary ks V1 V1 where
  generic_ _ _ _ _ _ = implies @ks @GenericEmptyProfunctor zero
  {-# INLINE generic_ #-}

instance ks |- GenericUnitProfunctor => ADT_ nullary unary ks U1 U1 where
  generic_ _ _ _ _ _ = implies @ks @GenericUnitProfunctor unit
  {-# INLINE generic_ #-}

instance (ks |- GenericSumProfunctor, ADT_ nullary unary ks f f', ADT_ nullary unary ks g g') => ADT_ nullary unary ks (f :+: g) (f' :+: g') where
  generic_ for f for1 f1 p1 = implies @ks @GenericSumProfunctor
    (plus (generic_ @nullary @unary @ks for f for1 f1 p1) (generic_ @nullary @unary @ks for f for1 f1 p1))
  {-# INLINE generic_ #-}

instance (ks |- GenericProductProfunctor, ADT_ nullary unary ks f f', ADT_ nullary unary ks g g') => ADT_ nullary unary ks (f :*: g) (f' :*: g') where
  generic_ for f for1 f1 p1 = implies @ks @GenericProductProfunctor
    (mult (generic_ @nullary @unary @ks for f for1 f1 p1) (generic_ @nullary @unary @ks for f for1 f1 p1))
  {-# INLINE generic_ #-}

instance ks |- Profunctor => ADT_ Identity unary ks (K1 i v) (K1 i' v') where
  generic_ _ f _ _ _ = implies @ks @Profunctor (dimap unK1 K1 (runIdentity f))
  {-# INLINE generic_ #-}

instance ks |- GenericEmptyProfunctor => ADT_ Proxy unary ks (K1 i v) (K1 i' v) where
  generic_ _ _ _ _ _ = implies @ks @GenericEmptyProfunctor (dimap unK1 K1 identity)
  {-# INLINE generic_ #-}

instance (ks |- Profunctor, ADT_ nullary unary ks f f') => ADT_ nullary unary ks (M1 i c f) (M1 i' c' f') where
  generic_ for f for1 f1 p1 = implies @ks @Profunctor
    (dimap unM1 M1 (generic_ @nullary @unary @ks for f for1 f1 p1))
  {-# INLINE generic_ #-}

instance (ks |- Profunctor, ADT_ nullary Identity ks g g') => ADT_ nullary Identity ks (f :.: g) (f' :.: g') where
  generic_ for f for1 f1 p1 = implies @ks @Profunctor
    (dimap unComp1 Comp1 $ runIdentity f1 (generic_ @nullary @Identity @ks for f for1 f1 p1))
  {-# INLINE generic_ #-}

instance ks |- Profunctor => ADT_ nullary Identity ks Par1 Par1 where
  generic_ _ _ _ _ p = implies @ks @Profunctor
    (dimap unPar1 Par1 (runIdentity p))
  {-# INLINE generic_ #-}

instance ks |- Profunctor => ADT_ nullary Identity ks (Rec1 f) (Rec1 f') where
  generic_ _ _ _ f p = implies @ks @Profunctor
    (dimap unRec1 Rec1 (runIdentity (f <*> p)))
  {-# INLINE generic_ #-}


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

record :: forall c p t t'. (ADTRecord t t', Constraints t t' c, GenericRecordProfunctor p)
       => (forall s s'. c s s' => p s s') -> p t t'
record f = dimap from to $ generic' @RecordProfunctor @c f
{-# INLINE record #-}

record1 :: forall c p t t' a b. (ADTRecord1 t t', Constraints1 t t' c, GenericRecordProfunctor p)
        => (forall d e s s'. c s s' => p d e -> p (s d) (s' e)) -> p a b -> p (t a) (t' b)
record1 f p = dimap from1 to1 $ generic1' @RecordProfunctor @c f p
{-# INLINE record1 #-}

record01 :: forall c0 c1 p t t' a b. (ADTRecord1 t t', Constraints01 t t' c0 c1, GenericRecordProfunctor p)
         => (forall s s'. c0 s s' => p s s') -> (forall d e s s'. c1 s s' => p d e -> p (s d) (s' e)) -> p a b -> p (t a) (t' b)
record01 k f p = dimap from1 to1 $ generic01' @RecordProfunctor @c0 @c1 k f p
{-# INLINE record01 #-}

nonEmpty :: forall c p t t'. (ADTNonEmpty t t', Constraints t t' c, GenericNonEmptyProfunctor p)
         => (forall s s'. c s s' => p s s') -> p t t'
nonEmpty f = dimap from to $ generic' @NonEmptyProfunctor @c f
{-# INLINE nonEmpty #-}

nonEmpty1 :: forall c p t t' a b. (ADTNonEmpty1 t t', Constraints1 t t' c, GenericNonEmptyProfunctor p)
          => (forall d e s s'. c s s' => p d e -> p (s d) (s' e)) -> p a b -> p (t a) (t' b)
nonEmpty1 f p = dimap from1 to1 $ generic1' @NonEmptyProfunctor @c f p
{-# INLINE nonEmpty1 #-}

nonEmpty01 :: forall c0 c1 p t t' a b. (ADTNonEmpty1 t t', Constraints01 t t' c0 c1, GenericNonEmptyProfunctor p)
           => (forall s s'. c0 s s' => p s s') -> (forall d e s s'. c1 s s' => p d e -> p (s d) (s' e)) -> p a b -> p (t a) (t' b)
nonEmpty01 k f p = dimap from1 to1 $ generic01' @NonEmptyProfunctor @c0 @c1 k f p
{-# INLINE nonEmpty01 #-}

generic :: forall c p t t'. (ADT t t', Constraints t t' c, GenericProfunctor p)
        => (forall s s'. c s s' => p s s') -> p t t'
generic f = dimap from to $ generic' @ADTProfunctor @c f
{-# INLINE generic #-}

generic1 :: forall c p t t' a b. (ADT1 t t', Constraints1 t t' c, GenericProfunctor p)
         => (forall d e s s'. c s s' => p d e -> p (s d) (s' e)) -> p a b -> p (t a) (t' b)
generic1 f p = dimap from1 to1 $ generic1' @ADTProfunctor @c f p
{-# INLINE generic1 #-}

generic01 :: forall c0 c1 p t t' a b. (ADT1 t t', Constraints01 t t' c0 c1, GenericProfunctor p)
          => (forall s s'. c0 s s' => p s s') -> (forall d e s s'. c1 s s' => p d e -> p (s d) (s' e)) -> p a b -> p (t a) (t' b)
generic01 k f p = dimap from1 to1 $ generic01' @ADTProfunctor @c0 @c1 k f p
{-# INLINE generic01 #-}

-- | `Constraints` is a constraint type synonym, containing the constraint
-- requirements for an instance for `t` of class `c`.
-- It requires an instance of class `c` for each component of `t`.
type Constraints t t' c = Constraints' (Rep t) (Rep t') c AnyType

type Constraints1 t t' c = Constraints' (Rep1 t) (Rep1 t') AnyType c

type Constraints01 t t' c0 c1 = Constraints' (Rep1 t) (Rep1 t') c0 c1

-- | `ADTRecord` is a constraint type synonym. An instance is an `ADT` with *exactly* one constructor.
type ADTRecord t t' = (Generic t, Generic t', ADTRecord' (Rep t) (Rep t'), Constraints t t' AnyType)

type ADTRecord1 t t' = (Generic1 t, Generic1 t', ADTRecord1' (Rep1 t) (Rep1 t'), Constraints1 t t' AnyType)

-- | `ADTNonEmpty` is a constraint type synonym. An instance is an `ADT` with *at least* one constructor.
type ADTNonEmpty t t' = (Generic t, Generic t', ADTNonEmpty' (Rep t) (Rep t'), Constraints t t' AnyType)

type ADTNonEmpty1 t t' = (Generic1 t, Generic1 t', ADTNonEmpty1' (Rep1 t) (Rep1 t'), Constraints1 t t' AnyType)

-- | `ADT` is a constraint type synonym. The `Generic` instance can be derived,
-- and any generic representation will be an instance of `ADT'` and `AnyType`.
type ADT t t' = (Generic t, Generic t', ADT' (Rep t) (Rep t'), Constraints t t' AnyType)

type ADT1 t t' = (Generic1 t, Generic1 t', ADT1' (Rep1 t) (Rep1 t'), Constraints1 t t' AnyType)

class AnyType a b
instance AnyType a b

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


data Pair a = Pair a a
instance Functor Pair where
  fmap f (Pair a b) = Pair (f a) (f b)
  {-# INLINE fmap #-}
  
infixr 9 .:
(.:) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.:) = (.) . (.)
{-# INLINE (.:) #-}

