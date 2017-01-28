{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, ConstraintKinds, TypeOperators, FlexibleContexts, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances #-}

import Generics.OneLiner

import Data.Monoid
-- import Control.Lens (Traversal')
-- import Data.Typeable
import Control.Applicative
import Control.DeepSeq
import Test.SmallCheck.Series
import Control.Monad.Logic.Class
import Control.Monad
import Data.Hashable
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Void
import Data.Binary
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen


-- http://hackage.haskell.org/package/deepseq-generics-0.1.1.1/docs/src/Control-DeepSeq-Generics.html
-- This would work if the monoid instance of () would have been strict, now it doesn't...
grnf :: (ADT t, Constraints t NFData) => t -> ()
grnf = gfoldMap (For :: For NFData) rnf


-- http://hackage.haskell.org/package/smallcheck-1.1.1/docs/src/Test-SmallCheck-Series.html
newtype Fair m a = Fair { runFair :: Series m a } deriving Functor
instance MonadLogic m => Applicative (Fair m) where
  pure a = Fair $ pure a
  Fair fs <*> Fair as = Fair $ fs <~> as
instance MonadLogic m => Alternative (Fair m) where
  empty = Fair mzero
  Fair l <|> Fair r = Fair $ l \/ r

gseries :: forall t m. (ADT t, Constraints t (Serial m), MonadLogic m) => Series m t
gseries = decDepth $ runFair $ createA (For :: For (Serial m)) (Fair series)

newtype CoSeries m a = CoSeries { runCoSeries :: forall r. Series m r -> Series m (a -> r) }
instance Contravariant (CoSeries m) where
  contramap f (CoSeries g) = CoSeries $ fmap (. f) . g
instance Divisible (CoSeries m) where
  divide f (CoSeries g) (CoSeries h) = CoSeries $ \rs -> (\bcr -> uncurry bcr . f) <$> g (h rs)
  conquer = CoSeries constM
instance MonadLogic m => Decidable (CoSeries m) where
  choose f (CoSeries g) (CoSeries h) = CoSeries $ \rs -> (\br cr -> either br cr . f) <$> g rs <~> h rs
  lose f = CoSeries $ \_ -> return $ absurd . f

gcoseries :: forall t m r. (ADT t, Constraints t (CoSerial m), MonadLogic m)
          => Series m r -> Series m (t -> r)
gcoseries = runCoSeries $ consume (For :: For (CoSerial m)) (CoSeries coseries)


-- http://hackage.haskell.org/package/hashable-1.2.2.0/docs/src/Data-Hashable-Generic.html
ghashWithSalt :: (ADT t, Constraints t Hashable) => Int -> t -> Int
ghashWithSalt = flip $ \t -> flip hashWithSalt (ctorIndex t) .
  appEndo (gfoldMap (For :: For Hashable) (Endo . flip hashWithSalt) t)

-- http://hackage.haskell.org/package/binary-0.7.2.1/docs/Data-Binary.html
gget :: (ADT t, Constraints t Binary) => Get t
gget = getWord8 >>= \ix -> getCompose (createA (For :: For Binary) (Compose [get])) !! fromEnum ix

gput :: (ADT t, Constraints t Binary) => t -> Put
gput t = putWord8 (toEnum (ctorIndex t)) <> gfoldMap (For :: For Binary) put t

-- https://hackage.haskell.org/package/QuickCheck-2.8.1/docs/Test-QuickCheck-Arbitrary.html
newtype CoArb a = CoArb { unCoArb :: forall b. a -> Gen b -> Gen b }
instance Contravariant CoArb where
  contramap f (CoArb g) = CoArb $ \a -> g (f a)
instance Divisible CoArb where
  divide f (CoArb g) (CoArb h) = CoArb $ \a -> case f a of
    (b, c) -> g b . h c
  conquer = CoArb $ const id
instance Decidable CoArb where
  choose f (CoArb g) (CoArb h) = CoArb $ \a -> case f a of
    Left b -> variant (0::Int) . g b
    Right c -> variant (1::Int) . h c
  lose f = CoArb $ absurd . f

gcoarbitrary :: (ADT t, Constraints t CoArbitrary) => t -> Gen b -> Gen b
gcoarbitrary = unCoArb $ consume (For :: For CoArbitrary) (CoArb coarbitrary)


liftCompareDefault :: (ADT1 f, Constraints1 f Ord1) => (a -> a -> Ordering) -> f a -> f a -> Ordering
liftCompareDefault = mzipWith1 (For :: For Ord1) liftCompare

infixr 9 .:
(.:) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.:) = (.) . (.)

liftEqDefault :: (ADT1 f, Constraints1 f Eq1) => (a -> a -> Bool) -> f a -> f a -> Bool
liftEqDefault = (getAll .:) . mzipWith1 (For :: For Eq1) ((All .:) . liftEq . (getAll .:)) . (All .:)
