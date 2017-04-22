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
import Data.Profunctor
import Data.Tagged


type family Constraints' (t :: * -> *) (c :: * -> Constraint) :: Constraint
type instance Constraints' V1 c = ()
type instance Constraints' U1 c = ()
type instance Constraints' (f :+: g) c = (Constraints' f c, Constraints' g c)
type instance Constraints' (f :*: g) c = (Constraints' f c, Constraints' g c)
type instance Constraints' (K1 i a) c = c a
type instance Constraints' (M1 i t f) c = Constraints' f c

type family ProfunctorConstraints' (t :: * -> *) (p :: * -> * -> *) :: Constraint
type instance ProfunctorConstraints' V1 p = GenericProfunctor p
type instance ProfunctorConstraints' U1 p = GenericRecordProfunctor p
type instance ProfunctorConstraints' (f :+: g) p
  = (GenericNonEmptyProfunctor p, ProfunctorConstraints' f p, ProfunctorConstraints' g p)
type instance ProfunctorConstraints' (f :*: g) p
  = (GenericRecordProfunctor p, ProfunctorConstraints' f p, ProfunctorConstraints' g p)
type instance ProfunctorConstraints' (K1 i c) p = GenericRecordProfunctor p
type instance ProfunctorConstraints' (M1 i t f) p
  = (Profunctor p, ProfunctorConstraints' f p)

type family ProfunctorConstraints1' (t :: * -> *) (p :: * -> * -> *) :: Constraint
type instance ProfunctorConstraints1' V1 p = GenericProfunctor p
type instance ProfunctorConstraints1' U1 p = GenericRecordProfunctor p
type instance ProfunctorConstraints1' (f :+: g) p
  = (GenericNonEmptyProfunctor p, ProfunctorConstraints1' f p, ProfunctorConstraints1' g p)
type instance ProfunctorConstraints1' (f :*: g) p
  = (GenericRecordProfunctor p, ProfunctorConstraints1' f p, ProfunctorConstraints1' g p)
type instance ProfunctorConstraints1' (f :.: g) p
  = (Profunctor p, ProfunctorConstraints1' g p)
type instance ProfunctorConstraints1' Par1 p = Profunctor p
type instance ProfunctorConstraints1' (Rec1 f) p = GenericProfunctor p
type instance ProfunctorConstraints1' (K1 i c) p = GenericProfunctor p
type instance ProfunctorConstraints1' (M1 i t f) p
  = (Profunctor p, ProfunctorConstraints1' f p)

class ADT' (t :: * -> *) where
  generic' :: (Constraints' t c, ProfunctorConstraints' t p)
    => for c -> (forall s. c s => p s s) -> p (t x) (t x)

instance ADT' V1 where generic' _ _ = zero
instance ADT' U1 where generic' _ _ = unit
instance (ADT' f, ADT' g) => ADT' (f :+: g) where generic' for f = plus (generic' for f) (generic' for f)
instance (ADT' f, ADT' g) => ADT' (f :*: g) where generic' for f = mult (generic' for f) (generic' for f)
instance ADT' (K1 i v) where generic' _ = dimap unK1 K1
instance ADT' f => ADT' (M1 i t f) where generic' for f = dimap unM1 M1 (generic' for f)

type family Constraints1' (t :: * -> *) (c :: (* -> *) -> Constraint) :: Constraint
type instance Constraints1' V1 c = ()
type instance Constraints1' U1 c = ()
type instance Constraints1' (f :+: g) c = (Constraints1' f c, Constraints1' g c)
type instance Constraints1' (f :*: g) c = (Constraints1' f c, Constraints1' g c)
type instance Constraints1' (f :.: g) c = (c f, Constraints1' g c)
type instance Constraints1' Par1 c = ()
type instance Constraints1' (Rec1 f) c = c f
type instance Constraints1' (K1 i v) c = ()
type instance Constraints1' (M1 i t f) c = Constraints1' f c

class ADT1' (t :: * -> *) where
  generic1' :: (Constraints1' t c, ProfunctorConstraints1' t p)
    => for c -> (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)

instance ADT1' V1 where generic1' _ _ _ = zero
instance ADT1' U1 where generic1' _ _ _ = unit
instance (ADT1' f, ADT1' g) => ADT1' (f :+: g) where generic1' for f p = plus (generic1' for f p) (generic1' for f p)
instance (ADT1' f, ADT1' g) => ADT1' (f :*: g) where generic1' for f p = mult (generic1' for f p) (generic1' for f p)
instance ADT1' g => ADT1' (f :.: g) where generic1' for f p = dimap unComp1 Comp1 $ f (generic1' for f p)
instance ADT1' Par1 where generic1' _ _ = dimap unPar1 Par1
instance ADT1' (Rec1 f) where generic1' _ f p = dimap unRec1 Rec1 (f p)
instance ADT1' (K1 i v) where generic1' _ _ _ = dimap unK1 K1 identity
instance ADT1' f => ADT1' (M1 i t f) where generic1' for f p = dimap unM1 M1 (generic1' for f p)

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

newtype Zip f a b = Zip { runZip :: a -> a -> f b }
instance Functor f => Profunctor (Zip f) where
  dimap f g (Zip h) = Zip $ \a1 a2 -> fmap g (h (f a1) (f a2))
instance Applicative f => GenericRecordProfunctor (Zip f) where
  unit = Zip $ \_ _ -> pure U1
  mult (Zip f) (Zip g) = Zip $ \(al :*: ar) (bl :*: br) -> (:*:) <$> f al bl <*> g ar br
instance Alternative f => GenericNonEmptyProfunctor (Zip f) where
  plus (Zip f) (Zip g) = Zip h where
    h (L1 a) (L1 b) = fmap L1 (f a b)
    h (R1 a) (R1 b) = fmap R1 (g a b)
    h _ _ = empty
instance Alternative f => GenericProfunctor (Zip f) where
  zero = Zip absurd
  identity = Zip $ \_ _ -> empty

inm2 :: (t -> t -> m) -> t -> t -> Compose Maybe (Const m) a
inm2 f = Compose .: Just .: Const .: f
outm2 :: Monoid m => (t -> t -> Compose Maybe (Const m) a) -> t -> t -> m
outm2 f = maybe mempty getConst .: getCompose .: f

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

generic :: ADTConstraints t p c
        => for c -> (forall s. c s => p s s) -> p t t
generic for f = dimap from to $ generic' for f

generic1 :: ADTConstraints1 t p c
         => for c -> (forall d e s. c s => p d e -> p (s d) (s e)) -> p a b -> p (t a) (t b)
generic1 for f p = dimap from1 to1 $ generic1' for f p

type ADTConstraints t p c = (ADT t p, Constraints t c)
type ADTConstraints1 t p c = (ADT1 t p, Constraints1 t c)

type ProfunctorConstraints t p = (ProfunctorConstraints' (Rep t) p, Profunctor p)
type ProfunctorConstraints1 t p = (ProfunctorConstraints1' (Rep1 t) p, Profunctor p)

-- | `Constraints` is a constraint type synonym, containing the constraint
-- requirements for an instance for `t` of class `c`.
-- It requires an instance of class `c` for each component of `t`.
type Constraints t c = Constraints' (Rep t) c

type Constraints1 t c = Constraints1' (Rep1 t) c

-- | `ADT` is a constraint type synonym. The `Generic` instance can be derived,
-- and any generic representation will be an instance of `ADT'` and `AnyType`.
-- @'ProfunctorConstraints' t@ reduces to 'GenericRecordProfunctor',
-- 'GenericNonEmptyProfunctor', or 'GenericProfunctor', depending on the number
-- of constructors of @t@.
--
-- The following list shows how to satisfy 'ADT' constraints used in one-liner.
--
-- For instance, @'ADT' t ('Clown' f)@ is entailed by @'Divisible' f@ if @t@ is
-- a generic data type with a unique constructor, and by @'Decidable' f@
-- in other cases (0 or more constructors).
--
-- The constraints @'ADT' t 'Costar'@ and @'ADT' t 'Tagged'@ are only satisfied
-- by types @t@ with a unique constructor.
--
-- @
-- 'ADT' t ('Clown'  f) -: 'Divisible' f    -- if t has a unique constructor
--                  -: 'Decidable' f    -- otherwise
-- 'ADT' t ('Costar' f) -: 'Functor' f      -- if t has a unique constructor
-- 'ADT' t ('Joker'  f) -: 'Applicative' f  -- if t has a unique constructor
--                  -: 'Alternative' f  -- otherwise
-- 'ADT' t ('Star'   f) -: 'Applicative' f
-- 'ADT' t ('Zip'    f) -: 'Applicative' f  -- if t has a unique constructor
--                  -: 'Alternative' f  -- otherwise
--
-- 'ADT' t 'Tagged' -: ()                 -- if t has a unique constructor
-- 'ADT' t (->)   -: ()
--
-- 'ADT' t ('Star' ('Const' m))               -: 'Monoid' m
-- 'ADT' t ('Zip' ('Compose' 'Maybe' ('Const' m)) -: 'Monoid' m
-- @
type ADT t p = (Generic t, ADT' (Rep t), Constraints t AnyType, ProfunctorConstraints t p)

type ADT1 t p = (Generic1 t, ADT1' (Rep1 t), Constraints1 t AnyType, ProfunctorConstraints1 t p)

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
ctorIndex :: ADT t Ctor => t -> Int
ctorIndex = index $ generic (For :: For AnyType) (Ctor (const 0) 1)

ctorIndex1 :: ADT1 t Ctor => t a -> Int
ctorIndex1 = index $ generic1 (For :: For AnyType) (const $ Ctor (const 0) 1) (Ctor (const 0) 1)

-- | Any type is instance of `AnyType`, you can use it with @For :: For AnyType@
-- if you don't actually need a class constraint.
class AnyType a
instance AnyType a

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
-- A constraint @'FunConstraint' t c@ is equivalent to the conjunction of
-- constraints @c s@ for every argument type of @t@.
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

infixr 9 .:
(.:) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.:) = (.) . (.)
