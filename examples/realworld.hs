{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, ConstraintKinds, TypeOperators, FlexibleContexts, GeneralizedNewtypeDeriving #-}

import Generics.OneLiner

import Data.Monoid
import Control.Lens (Traversal')
import Data.Typeable
import Control.DeepSeq
import Test.SmallCheck.Series
import Control.Monad.Logic.Class
import Control.Applicative
import Control.Monad
import Data.Hashable
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Void


-- http://hackage.haskell.org/package/lens-4.3.3/docs/Generics-Deriving-Lens.html
whenCastableOrElse :: forall a b f. (Typeable a, Typeable b) => (b -> f b) -> (a -> f a) -> a -> f a
whenCastableOrElse f g = maybe g (\Refl -> f) (eqT :: Maybe (a :~: b))

tinplate :: forall t b. (Typeable b, Deep Typeable t) => Traversal' t b
tinplate f
  | isAtom (Proxy :: Proxy t) = f `whenCastableOrElse` pure
  | otherwise = gtraverse (For :: For (Deep Typeable)) $ f `whenCastableOrElse` tinplate f


-- http://hackage.haskell.org/package/deepseq-generics-0.1.1.1/docs/src/Control-DeepSeq-Generics.html
grnf :: (ADT t, Constraints t NFData) => t -> ()
grnf = gfoldMap (For :: For NFData) rnf


-- http://hackage.haskell.org/package/smallcheck-1.1.1/docs/src/Test-SmallCheck-Series.html
newtype Fair m a = Fair { runFair :: Series m a } deriving Functor
instance MonadLogic m => Applicative (Fair m) where
  pure a = Fair $ pure a
  Fair fs <*> Fair as = Fair $ fs <~> as

gseries :: forall t m. (ADT t, Constraints t (Serial m), MonadLogic m) => Series m t
gseries = foldr ((\/) . decDepth . runFair) mzero $ createA (For :: For (Serial m)) (Fair series)

newtype CoSeries m a = CoSeries { runCoSeries :: forall r. Series m r -> Series m (a -> r) }
instance Contravariant (CoSeries m) where
  contramap f (CoSeries g) = CoSeries $ fmap (. f) . g
instance MonadLogic m => Divisible (CoSeries m) where
  divide f (CoSeries g) (CoSeries h) = CoSeries $ \rs -> do
    rs' <- fixDepth rs
    f2 <- decDepthChecked (constM $ constM rs') (g $ h rs')
    return $ uncurry f2 . f
  conquer = CoSeries constM
instance MonadLogic m => Decidable (CoSeries m) where
  choose f (CoSeries g) (CoSeries h) = CoSeries $ \rs ->
    (\br cr -> either br cr . f) <$> g rs <~> h rs
  lose f = CoSeries $ \_ ->
    return $ absurd . f

gcoseries :: forall t m r. (ADT t, Constraints t (CoSerial m), MonadLogic m)
          => Series m r -> Series m (t -> r)
gcoseries = runCoSeries $ consume (For :: For (CoSerial m)) (CoSeries coseries)


-- http://hackage.haskell.org/package/hashable-1.2.2.0/docs/src/Data-Hashable-Generic.html
ghashWithSalt :: (ADT t, Constraints t Hashable) => Int -> t -> Int
ghashWithSalt = flip $ \t -> flip hashWithSalt (ctorIndex t) .
  appEndo (gfoldMap (For :: For Hashable) (Endo . flip hashWithSalt) t)
