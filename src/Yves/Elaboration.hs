{-# LANGUAGE LambdaCase #-}

module Yves.Elaboration where

import Control.Applicative (Applicative (..))
import Control.Monad (Monad (..))
import Control.Monad qualified as Monad
import Control.Monad.State.Strict qualified as State
import Data.Collection (Collection (..))
import Data.Maybe qualified as Maybe
import Yves.Core.YTerm qualified as Core
import Yves.Elaboration.Monad (Elab)
import Yves.Elaboration.Monad qualified as Elab
import Yves.YTerm
import qualified Control.Monad.Reader as Reader
import Data.Function (($))
import qualified Yves.Core.Level as Level
import Control.Monad.Scoped.Free ((@))
import qualified Yves.Unification as Unification

elabInfer ::
  (Collection s) => YTerm (Key s) v -> Elab s v (Core.YTerm v, Core.YType v)
elabInfer = \case
  Var x -> do
    ty <- Reader.asks ($ x)
    return (Core.Var x, ty)
  MetaVar m -> do
    Maybe.Just sol <- State.gets (?! m)
    return sol
  YTType l -> pure (Core.YTType l, Core.YTType (Level.ofType l))
  a :~>: b -> do
    (a', Core.YTType l) <- elabInfer a
    (b', Core.YTType l') <- Elab.scope a' (elabInfer b)
    return (a' Core.:~>: b', Core.YTType (Level.ofPi l l'))
  YTAbs a b -> do
    (a', Core.YTType _) <- elabInfer a
    (b', t) <- Elab.scope a' (elabInfer b)
    return (Core.YTAbs a' b', a' Core.:~>: t)
  f :@: t -> do
    (f', a Core.:~>: b) <- elabInfer f
    t' <- elabCheck (t, a)
    return (f' Core.:@: t', b @ t')
  _ -> Monad.fail ""

elabCheck ::
  (Collection s) => (YTerm (Key s) v, Core.YType v) -> Elab s v (Core.YTerm v)
elabCheck = \case
  (t, ty) -> do
    (t', ty') <- elabInfer t
    Unification.unify ty ty'
    return t'
