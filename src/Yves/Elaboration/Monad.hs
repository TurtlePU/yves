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

type Ctx v = v -> Core.YType v

type Sub s v = s (Core.YTerm v, Core.YType v)

newtype Elab s v a = Elab {elab :: Ctx v -> Sub s v -> Maybe (a, Sub s v)}
  deriving (Functor)
  deriving
    ( Applicative,
      Alternative,
      Monad,
      MonadFail,
      MonadPlus,
      MonadState (Sub s v),
      MonadReader (Ctx v)
    )
    via (ReaderT (Ctx v) (StateT (Sub s v) Maybe))

scope :: (Collection s) => Core.YType v -> Elab s (In v) a -> Elab s v a
scope ty Elab {..} = Elab \ctx sub ->
  fmap (prune . fmap (bitraverse down down))
    <$> elab (up . In.elim ty ctx) (bimap up up <$> sub)
  where
    up = fmap In.There
    down = traverse In.toMaybe
