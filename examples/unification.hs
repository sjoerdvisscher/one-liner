{-# LANGUAGE
    TypeOperators
  , DeriveFunctor
  , DeriveGeneric
  , DeriveAnyClass
  , ConstraintKinds
  , FlexibleContexts
  , FlexibleInstances
  , TypeApplications
  , DefaultSignatures
  , UndecidableInstances
  #-}

import Control.Monad.Free (Free(..))
import Generics.OneLiner
import Generics.OneLiner.Classes
import GHC.Generics
import Data.Functor.Classes

data Failable a = Fail | Ok a deriving Show
instance Semigroup a => Semigroup (Failable a) where
  Fail <> _ = Fail
  _ <> Fail = Fail
  Ok a <> Ok b = Ok (a <> b)
instance Monoid a => Monoid (Failable a) where
  mempty = Ok mempty
  
class Unifyable f where
  unify :: Monoid m => (a -> a -> m) -> f a -> f a -> m
instance (ADT1 f, Constraints1 f Unifyable) => Unifyable f where
  unify = mzipWith1 @Unifyable unify
  
gunify :: (ADT1 f, Constraints1 f Unifyable) => Free f a -> Free f a -> Failable [(a, Free f a)]
gunify (Pure a) b = Ok [(a, b)]
gunify a (Pure b) = Ok [(b, a)]
gunify (Free a) (Free b) = mzipWith1' @Unifyable Fail unify gunify a b

data Lang a = Add a a | Int deriving (Show, Functor, Generic1)
instance Show1 Lang where
    liftShowsPrec _ _ _ Int = (++ "Int")
    -- liftShowsPrec _ _ d (Int x) =
        -- showsUnaryWith showsPrec "Int" d x
    liftShowsPrec sp _ d (Add x y) =
        showsBinaryWith sp sp "Add" d x y