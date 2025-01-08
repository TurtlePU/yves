{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

module Data.Named where

import Control.Monad.Scoped.Free qualified as Scoped
import Control.Monad.Scoped.Free.In qualified as In
import Data.Biapplicative (Bifunctor (..))
import Data.Collection (Collection (..))
import Data.Collection qualified as Collection
import Data.Either (Either)
import Data.Either qualified as Either
import Data.Eq (Eq (..))
import Data.Function (($), (.))
import Data.Functor (Functor (..))
import Data.Maybe qualified as Maybe
import Data.Tuple qualified as Tuple

data Named b n = NVar n | NTerm (b (n, Named b n) (Named b n))

instance (Bifunctor b) => Functor (Named b) where
  fmap f = go
    where
      go (NVar v) = NVar (f v)
      go (NTerm t) = NTerm (bimap (bimap f go) go t)

scoped ::
  (Bifunctor b, Collection f, Eq v) =>
  f (Scoped.Free b v) ->
  Named b (Either (Key f) v) ->
  Scoped.Free b v
scoped c (NVar (Either.Left v)) = Maybe.fromJust (c ?! v)
scoped _ (NVar (Either.Right v)) = Scoped.FVar v
scoped c (NTerm t) =
  let up :: (Functor f, Functor g) => f (g v) -> f (g (In.In v))
      up = fmap (fmap In.There)
      replaceIf k l = if l == In.There k then In.Here else l
      appended k d = Collection.insert k (Scoped.FVar In.Here) (up d)
   in Scoped.FTerm $
        bimap
          ( Tuple.uncurry \case
              Either.Left k -> scoped (appended k c) . up
              Either.Right k -> fmap (replaceIf k) . scoped (up c) . up
          )
          (scoped c)
          t
