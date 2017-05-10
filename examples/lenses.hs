-- This is a go at creating lenses with one-liner.
-- It is not a perfect match, but with some unsafeCoerce here and there it works.
{-# LANGUAGE RankNTypes, TypeOperators, DefaultSignatures, FlexibleContexts, DeriveGeneric, DeriveAnyClass, TypeApplications #-}
import Generics.OneLiner
import Data.Profunctor
import GHC.Generics
import Control.Applicative
import Unsafe.Coerce (unsafeCoerce)

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
type Key t = forall x. Lens (t x) (t x) x x

constLens :: x -> Lens s t a b -> x
constLens x _ = x

index :: f a -> Key f -> a
index f l = getConst $ l Const f


newtype Lensed s t a b = Lensed { getLensed :: Lens s t a b -> b }
instance Profunctor (Lensed s t) where
  dimap f g (Lensed ix) = Lensed $ \l -> g (ix (l . (fmap g .) . (. f)))
instance GenericUnitProfunctor (Lensed s t) where
  unit = Lensed (constLens U1)
instance GenericProductProfunctor (Lensed s t) where
  mult (Lensed a) (Lensed b) = Lensed (\l -> a (l . fstl) :*: b (l . sndl))

-- GenericProductProfunctor is a bit too polymorphic,
-- but we can use unsafeCoerce because the types will end up being the same anyway.
fstl :: Lens ((a :*: b) x) ((c :*: b') x') (a x) (c x')
fstl f (a :*: b) = (\c -> c :*: unsafeCoerce b) <$> f a
sndl :: Lens ((a :*: b) x) ((a' :*: c) x') (b x) (c x')
sndl f (a :*: b) = (\c -> unsafeCoerce a :*: c) <$> f b


class Repr f where

  lensed :: (Lens s t a b -> b) -> Lens s t (f a) (f b) -> f b
  default lensed :: (ADTRecord1 f, Constraints1 f Repr) => (Lens s t a b -> b) -> Lens s t (f a) (f b) -> f b
  lensed f = getLensed $ record1 @Repr (\(Lensed g) -> Lensed $ lensed g) (Lensed f)

  tabulate :: (Key f -> a) -> f a
  tabulate f = lensed (\l -> f (runKey (unsafeCoerce (Lens l)))) id

-- Two wrappers needed to make unsafeCoerce happy
newtype WrappedLens s t a b = Lens { runLens :: Lens s t a b }
newtype WrappedKey t = Key { runKey :: Key t }


data V3 a = V3 a a a deriving (Show, Generic1, Repr)
data V10 a = V10 a (V3 (V3 a)) deriving (Show, Generic1, Repr)

instance Functor V3 where
  fmap f v = tabulate (\k -> f (index v k))
instance Applicative V3 where
  pure a = tabulate (constLens a)
  fs <*> as = tabulate (\k -> index fs k (index as k))
instance Monad V3 where
  return = pure
  as >>= f = tabulate (\k -> f (as `index` k) `index` k)
