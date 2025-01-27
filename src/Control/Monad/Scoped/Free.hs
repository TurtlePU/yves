{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.Scoped.Free where

import Control.Applicative (Applicative (..))
import Control.Category ((<<<))
import Control.Monad (Monad (..), (<=<))
import Control.Monad qualified as Monad
import Control.Monad.Scoped.Free.In (In)
import Control.Monad.Scoped.Free.In qualified as In
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Eq (Eq)
import Data.Foldable (Foldable (..))
import Data.Function (($), (.))
import Data.Functor (Functor (..), (<$>))
import Data.Traversable (Traversable (..))
import GHC.Generics ((:.:) (..))

data Free b v
  = FVar v
  | FTerm {fterm :: b (Free b (In v)) (Free b v)}

deriving instance (Eq v, forall p q. (Eq p, Eq q) => Eq (b p q)) => Eq (Free b v)

lift :: Bifunctor b => Free b v -> Free b (In v)
lift = fmap In.There

teardown ::
  forall b f v.
  (Bifunctor b) =>
  (forall w. w -> f w) ->
  (forall w. b (f (In w)) (f w) -> f w) ->
  Free b v ->
  f v
teardown vf tf = go
  where
    go :: forall w. Free b w -> f w
    go (FVar v) = vf v
    go (FTerm t) = tf $ bimap go go t

teardownM ::
  forall b m f v.
  (Bitraversable b, Monad m) =>
  (forall w. w -> m (f w)) ->
  (forall w. b (f (In w)) (f w) -> m (f w)) ->
  Free b v ->
  m (f v)
teardownM vf tf =
  unComp1 . teardown (Comp1 . vf) (Comp1 <<< tf <=< bitraverse unComp1 unComp1)

infix 9 @

(@) :: (Bifunctor b) => Free b (In v) -> Free b v -> Free b v
f @ t = f >>= In.elim t pure

instance (Bifunctor b) => Functor (Free b) where
  fmap f (FVar v) = FVar (f v)
  fmap f (FTerm t) = FTerm $ bimap (fmap $ fmap f) (fmap f) t

instance (Bifunctor b) => Applicative (Free b) where
  pure = FVar
  (<*>) = Monad.ap

instance (Bifunctor b) => Monad (Free b) where
  FVar v >>= f = f v
  FTerm t >>= f =
    FTerm $
      bimap
        (>>= In.elim (FVar In.Here) (fmap In.There . f))
        (>>= f)
        t

foldrI :: (Foldable f) => (a -> b -> b) -> f a -> b -> b
foldrI f t x = foldr f x t

instance (Bifoldable b) => Foldable (Free b) where
  foldr f s (FVar v) = f v s
  foldr f s (FTerm t) = bifoldr (foldrI $ foldrI f) (foldrI f) s t

instance (Bitraversable b) => Traversable (Free b) where
  traverse f (FVar v) = FVar <$> f v
  traverse f (FTerm t) =
    FTerm <$> bitraverse (traverse $ traverse f) (traverse f) t
