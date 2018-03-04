-- http://hackage.haskell.org/package/lens-4.15.1/docs/Data-Data-Lens.html#v:tinplate
{-# LANGUAGE
  DataKinds,
  TypeFamilies,
  TypeOperators,
  FlexibleContexts,
  TypeApplications,
  FlexibleInstances,
  AllowAmbiguousTypes,
  ScopedTypeVariables,
  UndecidableInstances,
  MultiParamTypeClasses
  #-}

import Generics.OneLiner
import Data.Type.Equality

import Data.Functor.Identity


class TinplateHelper (p :: Bool) a b where
  trav' :: Applicative f => (a -> f a) -> b -> f b

instance TinplateHelper 'True a a where trav' f = f

instance {-# OVERLAPPABLE #-} (ADT b, Constraints b (TinplateAlias a)) => TinplateHelper 'False a b where
  trav' = tinplate

instance TinplateHelper 'False a Char where trav' _ = pure
instance TinplateHelper 'False a Double where trav' _ = pure
instance TinplateHelper 'False a Float where trav' _ = pure
instance TinplateHelper 'False a Int where trav' _ = pure
instance TinplateHelper 'False a Word where trav' _ = pure

class TinplateAlias a b where
  trav :: Applicative f => (a -> f a) -> b -> f b
instance TinplateHelper (a == b) a b => TinplateAlias a b where
  trav = trav' @(a == b)


tinplate :: forall a b f. (ADT b, Constraints b (TinplateAlias a), Applicative f) => (a -> f a) -> b -> f b
tinplate f = gtraverse @(TinplateAlias a) (trav f)
{-# INLINE tinplate #-}



test1, test2 :: [[(Char, Int)]] -> [[(Char, Int)]]
test1 = runIdentity . tinplate (Identity . f) where
  f :: Char -> Char
  f = succ
test2 = runIdentity . tinplate (Identity . f) where
  f :: Int -> Int
  f = succ

test12 :: [[(Char, Int)]]
test12 = test1 as ++ test2 as where as = [[('x', 1)], [('y', 2)]]
