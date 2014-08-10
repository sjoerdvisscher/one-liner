-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.Functions1
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
{-# LANGUAGE RankNTypes, ConstraintKinds, ScopedTypeVariables #-}
module Generics.OneLiner.Functions1 (
  -- * For all instances
    fmapADT
  , foldMapADT
  , traverseADT
  -- * For datatypes with one constructor
  , pureADT
  , apADT
  , bindADT
  , mfixADT
) where

import Generics.OneLiner.ADT1
import Control.Applicative
import Control.Monad.Fix
import Data.Monoid
import Data.Foldable
import Data.Traversable

fmapADT :: (ADT1 t, Constraints t Functor) => (a -> b) -> t a -> t b
fmapADT f ta = builds (For :: For Functor) (\fld -> f (ta ! fld)) (\fld -> fmap f (ta !~ fld)) `at` ta

foldMapADT :: (ADT1 t, Constraints t Foldable, Monoid m) => (a -> m) -> t a -> m
foldMapADT f ta = mbuilds (For :: For Foldable) (\fld -> f (ta ! fld)) (\fld -> foldMap f (ta !~ fld)) `at` ta

traverseADT :: (ADT1 t, Constraints t Traversable, Applicative f) => (a -> f b) -> t a -> f (t b)
traverseADT f ta = buildsA (For :: For Traversable) (\fld -> f (ta ! fld)) (\fld -> traverse f (ta !~ fld)) `at` ta

-- unfoldADT :: (ADT1 t, Constraints t Unfoldable, Unfolder f) => f a -> f (t a)
-- unfoldADT fa = choose $ buildsA (For :: For Unfoldable) (const fa) (const $ unfold fa)

pureADT :: (ADT1Record t, Constraints t Applicative) => a -> t a
pureADT a = build (For :: For Applicative) (const a) (const $ pure a)

apADT :: (ADT1Record t, Constraints t Applicative) => t (a -> b) -> t a -> t b
apADT tf ta = build (For :: For Applicative) (\fld -> (tf ! fld) (ta ! fld)) (\fld -> (tf !~ fld) <*> (ta !~ fld))

bindADT :: (ADT1Record t, Constraints t Monad) => t a -> (a -> t b) -> t b
bindADT ta f = build (For :: For Monad) (\fld -> f (ta ! fld) ! fld) (\fld -> (ta !~ fld) >>= ((!~ fld) . f))

mfixADT :: (ADT1Record t, Constraints t MonadFix) => (a -> t a) -> t a
mfixADT f = build (For :: For MonadFix) (\fld -> fix ((! fld) . f)) (\fld -> mfix ((!~ fld) . f))
