{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

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
import Data.Bool qualified as Bool
import Data.Either (Either)
import Data.Either qualified as Either
import Data.Eq (Eq (..))
import Data.Foldable (Foldable (..))
import Data.Function (($), (.))
import Data.Functor (Functor (..), (<$>))
import Data.Traversable (Traversable (..))
import GHC.Generics ((:.:) (..))

data Free b v where
  FPure :: v -> Free b v
  FLift :: (u -> v) -> Free b u -> Free b v
  FNode :: Node b v -> Free b v

newtype Node b v = Node {runNode :: b (Free b (In v)) (Free b v)}

pattern FVar :: Bifunctor b => v -> Free b v
pattern FVar x <- (peel -> Either.Left x) where
  FVar x = FPure x

pattern FTerm :: Bifunctor b => b (Free b (In v)) (Free b v) -> Free b v
pattern FTerm t <- (peel -> Either.Right (Node t)) where
  FTerm t = FNode (Node t)

{-# COMPLETE FVar, FTerm #-}

peel :: (Bifunctor b) => Free b v -> Either v (Node b v)
peel (FPure x) = Either.Left x
peel (FLift k t) = bimap k (fmap k) (peel t)
peel (FNode n) = Either.Right n

lift :: (Bifunctor b) => Free b v -> Free b (In v)
lift = fmap In.There

teardown ::
  forall b f v.
  (Bifunctor b, Functor f) =>
  (forall w. w -> f w) ->
  (forall w. b (f (In w)) (f w) -> f w) ->
  Free b v ->
  f v
teardown vf tf = go
  where
    go :: forall w. Free b w -> f w
    go (FPure v) = vf v
    go (FLift k t) = k <$> go t
    go (FNode n) = tf $ bimap go go (runNode n)

teardownM ::
  forall b m f v.
  (Bitraversable b, Monad m, Functor f) =>
  (forall w. w -> m (f w)) ->
  (forall w. b (f (In w)) (f w) -> m (f w)) ->
  Free b v ->
  m (f v)
teardownM vf tf =
  unComp1 . teardown (Comp1 . vf) (Comp1 <<< tf <=< bitraverse unComp1 unComp1)

infix 9 @

(@) :: (Bifunctor b) => Free b (In v) -> Free b v -> Free b v
f @ t = f >>= In.elim t pure

instance
  (Bifunctor b, Eq v, forall p q. (Eq p, Eq q) => Eq (b p q)) =>
  Eq (Free b v)
  where
  FLift k t == t' = fmap k t == t'
  t == FLift k t' = t == fmap k t'
  FPure x == FPure y = x == y
  FNode n == FNode n' = n == n'
  _ == _ = Bool.False

deriving newtype instance
  (Bifunctor b, Eq v, forall p q. (Eq p, Eq q) => Eq (b p q)) => Eq (Node b v)

instance (Bifunctor b) => Functor (Free b) where
  fmap f (FPure v) = FPure (f v)
  fmap f (FLift k t) = FLift (f . k) t
  fmap f (FNode n) = FNode (fmap f n)

instance (Bifunctor b) => Functor (Node b) where
  fmap f (Node n) = Node (bimap (fmap $ fmap f) (fmap f) n)

instance (Bifunctor b) => Applicative (Free b) where
  pure = FPure
  (<*>) = Monad.ap

instance (Bifunctor b) => Monad (Free b) where
  FPure v >>= f = f v
  FLift k t >>= f = t >>= (f . k)
  FNode n >>= f =
    FNode $
      Node $
        bimap
          (>>= In.elim (FPure In.Here) (fmap In.There . f))
          (>>= f)
          (runNode n)

instance (Bifoldable b) => Foldable (Free b) where
  foldr f s (FPure v) = f v s
  foldr f s (FLift k t) = foldr (f . k) s t
  foldr f s (FNode n) = foldr f s n

instance (Bifoldable b) => Foldable (Node b) where
  foldr f s (Node n) = bifoldr (foldrI $ foldrI f) (foldrI f) s n
    where
      foldrI g t x = foldr g x t

instance (Bitraversable b) => Traversable (Free b) where
  traverse f (FPure v) = FPure <$> f v
  traverse f (FLift k t) = traverse (f . k) t
  traverse f (FNode t) = FNode <$> traverse f t

instance (Bitraversable b) => Traversable (Node b) where
  traverse f (Node n) =
    Node <$> bitraverse (traverse $ traverse f) (traverse f) n
