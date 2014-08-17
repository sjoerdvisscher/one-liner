-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module is for writing generic functions on algebraic data types
-- of kind @*@. These data types must be an instance of the `Generic` type
-- class, which can be derived.
--
-----------------------------------------------------------------------------
{-# LANGUAGE
    GADTs
  , RankNTypes
  , TypeFamilies
  , TypeOperators
  , ConstraintKinds
  , FlexibleContexts
  , FlexibleInstances
  , ScopedTypeVariables
  , UndecidableInstances
  , MultiParamTypeClasses
  #-}
module Generics.OneLiner (
  -- * Producing values
  create, createA, ctorIndex,
  -- * Traversing values
  gmap, gfoldMap, gtraverse,
  -- * Combining values
  gzipWith, mzipWith, zipWithA,
  -- * Single constructor functions
  op0, op1, op2,
  -- * Types
  ADT, ADTRecord, Constraints, For(..), Deep, DeepConstraint, isAtom
) where

import GHC.Generics
import GHC.Prim (Constraint)
import Control.Applicative
import Data.Functor.Identity
import Data.Monoid
import Data.Typeable

type family Constraints' (t :: * -> *) (c :: * -> Constraint) :: Constraint
type instance Constraints' V1 c = ()
type instance Constraints' U1 c = ()
type instance Constraints' (f :+: g) c = (Constraints' f c, Constraints' g c)
type instance Constraints' (f :*: g) c = (Constraints' f c, Constraints' g c)
type instance Constraints' (K1 i v) c = c v
type instance Constraints' (M1 i t f) c = Constraints' f c

class ADT' (t :: * -> *) where
  ctorIndex' :: t x -> Int
  ctorIndex' _ = 0
  ctorCount :: proxy (t x) -> Int
  ctorCount _ = 1
  f0 :: (Constraints' t c, Applicative f)
     => for c -> (forall s. c s => f s) -> [f (t ())]
  f1 :: (Constraints' t c, Applicative f)
     => for c -> (forall s. c s => s -> f s) -> t x -> f (t x)
  f2 :: (Constraints' t c, Applicative f)
     => for c -> (forall s. c s => s -> s -> f s) -> t x -> t x -> Maybe (f (t x))

instance ADT' V1 where
  ctorCount _ = 0
  f0 _ _ = []
  f1 _ _ = pure
  f2 _ _ _ = Just . pure

instance (ADT' f, ADT' g) => ADT' (f :+: g) where
  ctorIndex' (L1 l) = ctorIndex' l
  ctorIndex' (R1 r) = ctorCount (undefined :: [f ()]) + ctorIndex' r
  ctorCount _ = ctorCount (undefined :: [f ()]) + ctorCount (undefined :: [g ()])
  f0 for f = map (fmap L1) (f0 for f) ++ map (fmap R1) (f0 for f)
  f1 for f (L1 l) = L1 <$> f1 for f l
  f1 for f (R1 r) = R1 <$> f1 for f r
  f2 for f (L1 a) (L1 b) = fmap (fmap L1) (f2 for f a b)
  f2 for f (R1 a) (R1 b) = fmap (fmap R1) (f2 for f a b)
  f2 _ _ _ _ = Nothing

instance ADT' U1 where
  f0 _ _ = [pure U1]
  f1 _ _ = pure
  f2 _ _ _ = Just . pure

instance (ADT' f, ADT' g) => ADT' (f :*: g) where
  f0 for f = [(:*:) <$> head (f0 for f) <*> head (f0 for f)]
  f1 for f (l :*: r) = (:*:) <$> f1 for f l <*> f1 for f r
  f2 for f (al :*: ar) (bl :*: br) = liftA2 (:*:) <$> f2 for f al bl <*> f2 for f ar br

instance ADT' (K1 i v) where
  f0 _ f = [K1 <$> f]
  f1 _ f (K1 v) = K1 <$> f v
  f2 _ f (K1 l) (K1 r) = Just $ K1 <$> f l r

instance ADT' f => ADT' (M1 i t f) where
  ctorIndex' = ctorIndex' . unM1
  ctorCount _ = ctorCount (undefined :: [M1 i t f ()])
  f0 for f = map (fmap M1) (f0 for f)
  f1 for f = fmap M1 . f1 for f . unM1
  f2 for f (M1 l) (M1 r) = fmap (fmap M1) (f2 for f l r)


class ADTRecord' (f :: * -> *) where
instance ADTRecord' U1
instance ADTRecord' (f :*: g)
instance ADTRecord' (K1 i v)
instance ADTRecord' f => ADTRecord' (M1 i t f)
instance ADTRecord' f => ADTRecord' (V1 :+: f)
instance ADTRecord' f => ADTRecord' (f :+: V1)

-- | `Constraints` is a constraint type synonym, containing the constraint requirements for an instance for `t` of class `c`.
-- It requires an instance of class `c` for each component of `t`.
type Constraints t c = Constraints' (Rep t) c

-- | `ADT` is a constraint type synonym. The `Generic` instance can be derived,
-- and any generic representation will be an instance of `ADT'`.
type ADT t = (Generic t, ADT' (Rep t))

-- | `ADTRecord` is a constraint type synonym. An instance is an `ADT` with exactly one constructor.
type ADTRecord t = (ADT t, ADTRecord' (Rep t))

-- | Tell the compiler which class we want to use in the traversal. Should be used like this:
--
-- > (For :: For Show)
--
-- Where @Show@ can be any class.
data For (c :: * -> Constraint) = For

-- | @Deep c@ recursively requires all parts of the datatype to be an instance of `c` and of `Generic`.
class DeepConstraint c t => Deep (c :: * -> Constraint) t where
instance DeepConstraint c t => Deep c t

-- http://stackoverflow.com/questions/14133121/can-i-constrain-a-type-family
-- | A trick to avoid GHC from detecting a cycle.
type family DeepConstraint (c :: * -> Constraint) t :: Constraint
type instance DeepConstraint c t = (c t, ADT t, Constraints t (Deep c), Constraints t c)

isAtom :: forall t proxy. (ADT t, Typeable t, Constraints t Typeable) => proxy t -> Bool
isAtom pt = case createA (For :: For Typeable) f :: [Const [Bool] t] of
  [Const [True]] -> True
  _ -> False
  where
    f :: forall a. Typeable a => Const [Bool] a
    f = Const [tRep == typeRep (undefined :: [a])]
    tRep = typeRep pt

-- | Create a value (one for each constructor), given how to construct the components.
--
-- @
-- `minBound` = `head` `$` `create` (`For` :: `For` `Bounded`) `minBound`
-- `maxBound` = `last` `$` `create` (`For` :: `For` `Bounded`) `maxBound`
-- @
create :: (ADT t, Constraints t c)
       => for c -> (forall s. c s => s) -> [t]
create for f = map runIdentity (createA for (Identity f))

-- | Create a value (one for each constructor), given how to construct the components, under an applicative effect.
--
-- Here's how to implement `get` from the `binary` package:
--
-- @
-- get = getWord8 `>>=` \\ix -> `createA` (`For` :: `For` Binary) get `!!` `fromEnum` ix
-- @
createA :: (ADT t, Constraints t c, Applicative f)
        => for c -> (forall s. c s => f s) -> [f t]
createA for f = map (fmap to) (f0 for f)

-- | Get the index in the lists returned by `create` and `createA` of the constructor of the given value.
--
-- For example, this is the implementation of `put` that generates the binary data that
-- the above implentation of `get` expects:
--
-- @
-- `put` t = `putWord8` (`toEnum` (`ctorIndex` t)) `<>` `gfoldMap` (`For` :: `For` `Binary`) `put` t
-- @
--
-- /Note that this assumes a straightforward `Monoid` instance of `Put` which `binary` unfortunately does not provide./
ctorIndex :: ADT t => t -> Int
ctorIndex = ctorIndex' . from

-- | Map over a structure, updating each component.
gmap :: (ADT t, Constraints t c)
     => for c -> (forall s. c s => s -> s) -> t -> t
gmap for f = runIdentity . gtraverse for (Identity . f)

-- | Map each component of a structure to a monoid, and combine the results.
--
-- If you have a class `Size`, which measures the size of a structure, then this could be the default implementation:
--
-- @
-- size = `succ` `.` `getSum` `.` `gfoldMap` (`For` :: `For` Size) (`Sum` `.` size)
-- @
gfoldMap :: (ADT t, Constraints t c, Monoid m)
         => for c -> (forall s. c s => s -> m) -> t -> m
gfoldMap for f = getConst . gtraverse for (Const . f)

-- | Map each component of a structure to an action, evaluate these actions from left to right, and collect the results.
gtraverse :: (ADT t, Constraints t c, Applicative f)
          => for c -> (forall s. c s => s -> f s) -> t -> f t
gtraverse for f = fmap to . f1 for f . from

-- | Combine two values by combining each component of the structures with the given function.
-- Returns `Nothing` if the constructors don't match.
gzipWith :: (ADT t, Constraints t c)
         => for c -> (forall s. c s => s -> s -> s) -> t -> t -> Maybe t
gzipWith for f l r = runIdentity <$> zipWithA for (\x y -> Identity (f x y)) l r

-- | Combine two values by combining each component of the structures to a monoid, and combine the results.
-- Returns `mempty` if the constructors don't match.
--
-- @
-- `compare` s t = `compare` (`ctorIndex` s) (`ctorIndex` t) `<>` `mzipWith` (`For` :: `For` `Ord`) `compare` s t
-- @
mzipWith :: (ADT t, Constraints t c, Monoid m)
         => for c -> (forall s. c s => s -> s -> m) -> t -> t -> m
mzipWith for f l r = maybe mempty getConst $ zipWithA for (\x y -> Const (f x y)) l r

-- | Combine two values by combining each component of the structures with the given function, under an applicative effect.
-- Returns `Nothing` if the constructors don't match.
zipWithA :: (ADT t, Constraints t c, Applicative f)
         => for c -> (forall s. c s => s -> s -> f s) -> t -> t -> Maybe (f t)
zipWithA for f l r = fmap (fmap to) (f2 for f (from l) (from r))

-- | Implement a nullary operator by calling the operator for each component.
--
-- @
-- `mempty` = `op0` (`For` :: `For` `Monoid`) `mempty`
-- `fromInteger` i = `op0` (`For` :: `For` `Num`) (`fromInteger` i)
-- @
op0 :: (ADTRecord t, Constraints t c)
    => for c -> (forall s. c s => s) -> t
op0 for f = head $ create for f

-- | Implement a unary operator by calling the operator on the components.
-- This is here for consistency, it is the same as `gmap`.
--
-- @
-- `negate` = `op1` (`For` :: `For` `Num`) `negate`
-- @
op1 :: (ADTRecord t, Constraints t c)
     => for c -> (forall s. c s => s -> s) -> t -> t
op1 = gmap

-- | Implement a binary operator by calling the operator on the components.
--
-- @
-- `mappend` = `op2` (`For` :: `For` `Monoid`) `mappend`
-- (`+`) = `op2` (`For` :: `For` `Num`) (`+`)
-- @
op2 :: (ADTRecord t, Constraints t c)
    => for c -> (forall s. c s => s -> s -> s) -> t -> t -> t
op2 for f l r = case gzipWith for f l r of
  Just t -> t
  Nothing -> error "op2: constructor mismatch should not be possible for ADTRecord"
