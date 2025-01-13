{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RecordWildCards #-}

module Yves.Elaboration.Monad where

import Control.Applicative (Alternative, Applicative)
import Control.Monad (Monad, MonadPlus)
import Control.Monad.Fail (MonadFail)
import Control.Monad.Reader (MonadReader)
import Control.Monad.Scoped.Free.In (In)
import Control.Monad.Scoped.Free.In qualified as In
import Control.Monad.State (MonadState)
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Monad.Trans.State.Strict (StateT (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Collection (Collection (..))
import Data.Function ((.))
import Data.Functor (Functor (..), (<$>))
import Data.Maybe (Maybe)
import Data.Traversable (Traversable (..))
import Yves.Core.YTerm qualified as Core
import Yves.YTerm

type Ctx m v = v -> YType m v

type Sub s v = s (Core.YTerm v, Core.YType v)

newtype Elab s m v a = Elab {elab :: Ctx m v -> Sub s v -> Maybe (a, Sub s v)}
  deriving (Functor)
  deriving
    ( Applicative,
      Alternative,
      Monad,
      MonadFail,
      MonadPlus,
      MonadState (Sub s v),
      MonadReader (Ctx m v)
    )
    via (ReaderT (Ctx m v) (StateT (Sub s v) Maybe))

scope :: (Collection s) => YType m v -> Elab s m (In v) a -> Elab s m v a
scope ty Elab {..} = Elab \ctx sub ->
  fmap (prune . fmap (bitraverse down down))
    <$> elab (up . In.elim ty ctx) (bimap up up <$> sub)
  where
    up :: Functor f => f a -> f (In a)
    up = fmap In.There
    down = traverse In.toMaybe
