-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.Classes
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
{-# LANGUAGE
    EmptyCase
  , LambdaCase
  , TypeOperators
  , MonoLocalBinds
  , FlexibleInstances
  , UndecidableInstances
  #-}
module Generics.OneLiner.Classes where

import GHC.Generics
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


class Profunctor p => GenericUnitProfunctor p where
  unit :: p (U1 a) (U1 a')

class Profunctor p => GenericProductProfunctor p where
  mult :: p (f a) (f' a') -> p (g a) (g' a') -> p ((f :*: g) a) ((f' :*: g') a')

class Profunctor p => GenericSumProfunctor p where
  plus :: p (f a) (f' a') -> p (g a) (g' a') -> p ((f :+: g) a) ((f' :+: g') a')

class Profunctor p => GenericEmptyProfunctor p where
  identity :: p a a
  zero :: p (V1 a) (V1 a')


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


newtype Zip f a b = Zip { runZip :: a -> a -> f b }
instance Functor f => Profunctor (Zip f) where
  dimap f g (Zip h) = Zip $ \a1 a2 -> fmap g (h (f a1) (f a2))
  {-# INLINE dimap #-}
instance Applicative f => GenericUnitProfunctor (Zip f) where
  unit = Zip $ \_ _ -> pure U1
  {-# INLINE unit #-}
instance Applicative f => GenericProductProfunctor (Zip f) where
  mult (Zip f) (Zip g) = Zip $ \(al :*: ar) (bl :*: br) -> (:*:) <$> f al bl <*> g ar br
  {-# INLINE mult #-}
instance Alternative f => GenericSumProfunctor (Zip f) where
  plus (Zip f) (Zip g) = Zip h where
    h (L1 a) (L1 b) = fmap L1 (f a b)
    h (R1 a) (R1 b) = fmap R1 (g a b)
    h _ _ = empty
  {-# INLINE plus #-}
instance Alternative f => GenericEmptyProfunctor (Zip f) where
  zero = Zip absurd
  {-# INLINE zero #-}
  identity = Zip $ \_ _ -> empty
  {-# INLINE identity #-}


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
