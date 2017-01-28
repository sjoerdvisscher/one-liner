-- http://hackage.haskell.org/package/lens-4.15.1/docs/Data-Data-Lens.html#v:tinplate
{-# LANGUAGE
  DataKinds,
  TypeFamilies,
  FlexibleContexts,
  FlexibleInstances,
  ScopedTypeVariables,
  UndecidableInstances,
  MultiParamTypeClasses
  #-}

import Generics.OneLiner
import Data.Proxy
import Data.Functor.Identity

class Tinplate' (p :: Bool) a b where
  trav' :: Applicative f => proxy p -> (a -> f a) -> b -> f b

instance Tinplate' 'True a a where trav' _ f = f

instance Tinplate' 'False a Char where trav' _ _ = pure
instance Tinplate' 'False a Double where trav' _ _ = pure
instance Tinplate' 'False a Float where trav' _ _ = pure
instance Tinplate' 'False a Int where trav' _ _ = pure
instance Tinplate' 'False a Word where trav' _ _ = pure

instance {-# OVERLAPPABLE #-} (ADT b, Constraints b (Tinplate a)) => Tinplate' 'False a b where
  trav' _ = tinplate

type family Equals a b :: Bool where
  Equals a a = 'True
  Equals a b = 'False

class Tinplate a b where
  trav :: Applicative f => (a -> f a) -> b -> f b

instance Tinplate' (Equals a b) a b => Tinplate a b where
  trav = trav' (Proxy :: Proxy (Equals a b))


tinplate :: forall a b f. (ADT b, Constraints b (Tinplate a), Applicative f) => (a -> f a) -> b -> f b
tinplate f = gtraverse (For :: For (Tinplate a)) (trav f)



test1, test2 :: [[(Char, Int)]] -> [[(Char, Int)]]
test1 = runIdentity . tinplate (Identity . f) where
  f :: Char -> Char
  f = succ
test2 = runIdentity . tinplate (Identity . f) where
  f :: Int -> Int
  f = succ

test12 :: [[(Char, Int)]]
test12 = test1 as ++ test2 as where as = [[('x', 1)], [('y', 2)]]
