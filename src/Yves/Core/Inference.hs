{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Yves.Core.Inference (infer) where

import Control.Applicative (Applicative (..))
import Control.Monad (Monad (..))
import Control.Monad.Scoped.Free qualified as Free
import Control.Monad.Scoped.Free.In (In (..))
import Control.Monad.Scoped.Free.In qualified as In
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Eq (Eq)
import Data.Function (($), (.))
import Data.Functor (Functor (..), (<$>))
import Data.Maybe (Maybe)
import Yves.Core.Evaluation qualified as Evaluation
import Yves.Core.Synthesis qualified as Synthesis
import Yves.Core.YTerm

data InferenceResult v = IResult
  { evalResult :: YTerm v,
    inferResult :: (v -> YType v) -> Maybe (YType v)
  }

infer :: (Eq v) => (v -> YType v) -> YTerm v -> Maybe (YType v)
infer ctx term = inferResult (impl term) ctx
  where
    impl :: (Eq w) => YTerm w -> InferenceResult w
    impl (Free.FVar v) = IResult (Var v) (pure . ($ v))
    impl (Free.FTerm t) = inferTerm (bimap impl impl t)

    inferTerm ::
      forall w.
      (Eq w) =>
      TermF (InferenceResult (In w)) (InferenceResult w) ->
      InferenceResult w
    inferTerm t =
      IResult
        { evalResult = Evaluation.evaluateF $ bimap evalResult evalResult t,
          inferResult = \c ->
            bitraverse
              (\r -> pure (evalResult r, inferResult r . liftCtx c))
              (\r -> (evalResult r,) <$> inferResult r c)
              t
              >>= Synthesis.synthesizeF
        }

    liftCtx :: (v -> YType v) -> YType v -> In v -> YType (In v)
    liftCtx c ty = fmap There . In.elim ty c
