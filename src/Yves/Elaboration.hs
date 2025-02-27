{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeOperators #-}

module Yves.Elaboration where

import Control.Applicative (Alternative, Applicative (..))
import Control.Monad (Monad (..))
import Control.Monad qualified as Monad
import Control.Monad.Fail (MonadFail)
import Control.Monad.Reader (MonadReader, ReaderT (..), asks)
import Control.Monad.Scoped.Free ((@))
import Control.Monad.Scoped.Free qualified as Free
import Control.Monad.Scoped.Free.In (In)
import Control.Monad.Scoped.Free.In qualified as In
import Control.Monad.State (MonadState, State)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.State (StateT (..))
import Data.Bifunctor.Sum qualified as Sum
import Data.Collection (Collection (..))
import Data.Eq (Eq (..))
import Data.Foldable (Foldable)
import Data.Function (($), (.))
import Data.Functor (Functor (..))
import Data.Functor.Identity (Identity (..))
import Data.Maybe (Maybe (..))
import Data.Traversable (Traversable (..))
import Yves.Core.Level qualified as Level
import Yves.Core.YTerm qualified as Core
import Yves.YTerm
import Prelude qualified

-- Elaboration example:
-- Term = W ... ...
-- eval : Term -> Type 0
-- Empty = (P : Type 0) -> P
-- Dec : (P : Type 0) -> Sigma (b : Bool) (if b then P else (P -> Empty))
-- prove : (t : Term) -> Dec (eval t)
-- tactic : (t : Term) (p : eval t) -> prove t = (true, p) -> eval t
--
-- tactic ?x ?y refl <- a + b + (c + d) = (a + b) + c + d
-- tactic ?x ?y $ [refl] <- ...
-- tactic ?x $ [?y, refl] <- ...
-- tactic $ [?x, ?y, refl] <- ...
-- Pi (t : Term) (p : eval t) -> prove t = (true, p) -> eval t
-- @ [?x, ?y, refl] === ...
-- Pi (p : eval ?x) -> prove ?x = (true, p) -> eval ?x
-- @ [?y, refl] === ... ; ?x : Term
-- prove ?x = (true, ?y) -> eval ?x @ [refl] === ... ; ?x : Term, ?y : eval ?x
-- eval ?x === ... ; ?x : Term, ?y : eval ?x, refl : prove ?x = (true, ?y)
-- eval ?x === ... & prove ?x === (true, ?y) ; ?x : Term, ?y : eval ?x

type Ctx m v = v -> YType m v

extend :: YType m v -> Ctx m v -> Ctx m (In v)
extend en ctx = fmap In.There . In.elim en ctx

data SubEntry m v = YTerm m v :| Maybe (YType m v)
  deriving (Functor, Foldable, Traversable)

type Sub s m v = s (SubEntry m v)

type ElabState s m v a = Sub s m v -> (Maybe a, Sub s m v)

scopeState :: (Collection s) => ElabState s m (In v) a -> ElabState s m v a
scopeState = (. premap) . (fmap postmap .)
  where
    premap :: (Functor s) => Sub s m v -> Sub s m (In v)
    premap = fmap (fmap In.There)

    postmap :: (Collection s) => Sub s m (In v) -> Sub s m v
    postmap = prune . fmap (traverse In.toMaybe)

newtype Elab s m v a = Elab {elab :: Ctx m v -> ElabState s m v a}
  deriving (Functor)
  deriving
    ( Applicative,
      Alternative,
      Monad,
      MonadFail,
      MonadState (Sub s m v),
      MonadReader (Ctx m v)
    )
    via (ReaderT (Ctx m v) (MaybeT (State (Sub s m v))))

scope :: (Collection s) => YType m v -> Elab s m (In v) a -> Elab s m v a
scope en = Elab . (. extend en) . (scopeState .) . elab

unify :: YTerm m v -> YTerm m v -> Elab s m v (YTerm m v)
unify = Prelude.error "TODO: unification"

bubble :: Core.YTerm v -> YTerm m v
bubble = Free.teardown Var (Free.FTerm . Sum.L2)

type ElabResult s m v = Elab s m v (Core.YTerm v, YType m v)

-- | TODO: add matching capability
match ::
  -- | computation to run after match
  ElabResult s m v ->
  -- | input type hint
  Maybe (YType m v) ->
  -- | resulting computation
  ElabResult s m v
match comp Nothing = comp
match comp (Just ty) = do
  (tm', ty') <- comp
  ty'' <- unify ty ty'
  return (tm', ty'')

elaborate ::
  (Collection s, Key s ~ m, Eq v) =>
  -- | head of a term to elaborate
  YTerm m v ->
  -- | result type hint
  Maybe (YType m v) ->
  -- | elaboration result
  ElabResult s m v
-- Inference mode
elaborate (Var v) = match do
  ty <- asks ($ v)
  return (Core.Var v, ty)
elaborate (YTType l) =
  match $
    return (Core.YTType l, YTType (Level.ofType l))
elaborate (a :~>: b) = match do
  (b', YTType lb) <- scope a (elaborate b Nothing)
  (a', YTType la) <- elaborate a Nothing
  return (a' Core.:~>: b', YTType (Level.ofPi la lb))
elaborate (YTAbs a f) = match do
  (a', YTType _) <- elaborate a Nothing
  (f', tf) <- scope a (elaborate f Nothing)
  return (Core.YTAbs a' f', a :~>: tf)
elaborate (_ :@: _) = Prelude.error "TODO: YTApp"
elaborate (a :*: b) = match do
  (a', YTType la) <- elaborate a Nothing
  (b', YTType lb) <- scope a (elaborate b Nothing)
  return (a' Core.:*: b', YTType (Level.ofSigma la lb))
elaborate (YTPair b f s) = match do
  (f', a) <- elaborate f Nothing
  (b', YTType _) <- scope a (elaborate b Nothing)
  (s', _) <- elaborate s (Just (b @ f))
  return (Core.YTPair b' f' s', a :*: b)
elaborate (YTFst _) = Prelude.error "TODO: YTFst"
elaborate (YTSnd _) = Prelude.error "TODO: YTSnd"
elaborate YTBool = match $ return (Core.YTBool, YTType Level.ofBool)
elaborate (YTBValue b) = match $ return (Core.YTBValue b, YTBool)
elaborate YTIf {} = Prelude.error "TODO: YTIf"
elaborate (YTIdType a x y) = match do
  (a', YTType l) <- elaborate a Nothing
  (x', _) <- elaborate x (Just a)
  (y', _) <- elaborate y (Just a)
  return (Core.YTIdType a' x' y', YTType (Level.ofId l))
elaborate (YTRefl a) = match do
  (a', ty) <- elaborate a Nothing
  return (Core.YTRefl a', YTIdType ty a a)
elaborate YTJ {} = Prelude.error "TODO: YTJ"
elaborate (YTW a b) = match do
  (a', YTType la) <- elaborate a Nothing
  (b', YTType lb) <- scope a (elaborate b Nothing)
  return (Core.YTW a' b', YTType (Level.ofW la lb))
elaborate YTTree {} = Prelude.error "TODO: YTTree inference"
elaborate YTRec {} = Prelude.error "TODO: YTRec"
-- Metavar solving
elaborate MetaVar {} = Prelude.error "TODO: Metavar solving"
-- Mode switch
elaborate (tm :!: ty) = match $ elaborate tm (Just ty)
-- If nothing suffices, fail.
elaborate _ = \_ -> Monad.fail ""
