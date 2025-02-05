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
import Data.Bool (otherwise)
import Data.Collection (Collection (..))
import Data.Eq (Eq (..))
import Data.Foldable (Foldable)
import Data.Function (($), (.))
import Data.Functor (Functor (..), (<$>))
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

data Arg m v
  = Arg (YTerm m v)
  | AFst
  | ASnd
  | AIf (YType m (In v)) (YTerm m v) (YTerm m v)
  | AJ (YType m v) (YTerm m (In v))
  | ARec (YType m (In v)) (YTerm m v)

shift :: [Arg m v] -> [Arg m (In v)]
shift = fmap impl
  where
    lift' :: YTerm m (In v) -> YTerm m (In (In v))
    lift' = fmap (fmap In.There)

    impl :: Arg m v -> Arg m (In v)
    impl (Arg t) = Arg (Free.lift t)
    impl AFst = AFst
    impl ASnd = ASnd
    impl (AIf g t e) = AIf (lift' g) (Free.lift t) (Free.lift e)
    impl (AJ ty tm) = AJ (Free.lift ty) (lift' tm)
    impl (ARec g s) = ARec (lift' g) (Free.lift s)

type ElabResult s m v = Elab s m v (Core.YTerm v, Core.YType v)

unify :: YTerm m v -> YTerm m v -> Elab s m v (YTerm m v)
unify = Prelude.error "TODO: unification"

bubble :: Core.YTerm v -> YTerm m v
bubble = Free.teardown Var (Free.FTerm . Sum.L2)

apply ::
  -- | accumulator term
  Core.YTerm v ->
  -- | type of an accumulator
  YType m v ->
  -- | arguments to apply (rib)
  [Arg m v] ->
  -- | result type hint
  Maybe (YType m v) ->
  -- | elaborated after application
  ElabResult s m v
apply srcTm srcTy srcArgs res = go (bubble srcTm) srcTy srcArgs
  where
    go _ ty0 [] = do
      _ <- case res of
        Just ty1 -> unify ty0 ty1
        Nothing -> pure ty0
      Prelude.error "TODO: application mode end"
    go _ _ (_ : _) = Prelude.error "TODO: application mode step"

-- | TODO: add matching capability
match ::
  -- | computation to run after match
  ElabResult s m v ->
  -- | input type hint
  Maybe (YType m v) ->
  -- | resulting computation
  ElabResult s m v
match comp Nothing = comp
match comp ty@(Just _) = do
  (tm', ty') <- comp
  apply tm' (bubble ty') [] ty

elaborate ::
  (Collection s, Key s ~ m, Eq v) =>
  -- | head of a term to elaborate
  YTerm m v ->
  -- | arguments to apply (rib)
  [Arg m v] ->
  -- | result type hint
  Maybe (YType m v) ->
  -- | elaboration result
  ElabResult s m v
-- Inference mode
elaborate (YTType l) [] = match $ return (Core.YTType l, Core.YTType (Level.ofType l))
elaborate (a :~>: b) [] = match do
  (b', Core.YTType lb) <- scope a (elaborate b [] Nothing)
  (a', Core.YTType la) <- elaborate a [] Nothing
  return (a' Core.:~>: b', Core.YTType (Level.ofPi la lb))
elaborate (YTAbs a f) [] = match do
  (f', tf) <- scope a (elaborate f [] Nothing)
  (a', Core.YTType _) <- elaborate a [] Nothing
  return (Core.YTAbs a' f', a' Core.:~>: tf)
elaborate (a :*: b) [] = match do
  (b', Core.YTType lb) <- scope a (elaborate b [] Nothing)
  (a', Core.YTType la) <- elaborate a [] Nothing
  return (a' Core.:*: b', Core.YTType (Level.ofSigma la lb))
elaborate (YTPair b f s) [] = match do
  (f', a) <- elaborate f [] Nothing
  (s', _) <- elaborate s [] (Just (b @ f))
  (b', Core.YTType _) <- scope (bubble a) (elaborate b [] Nothing)
  return (Core.YTPair b' f' s', a Core.:*: b')
elaborate YTBool [] = match $ return (Core.YTBool, Core.YTType Level.ofBool)
elaborate (YTBValue b) [] = match $ return (Core.YTBValue b, Core.YTBool)
elaborate (YTIdType a x y) [] = match do
  (x', _) <- elaborate x [] (Just a)
  (y', _) <- elaborate y [] (Just a)
  (a', Core.YTType l) <- elaborate a [] Nothing
  return (Core.YTIdType a' x' y', Core.YTType (Level.ofId l))
elaborate (YTRefl a) [] = match do
  (a', ty) <- elaborate a [] Nothing
  return (Core.YTRefl a', Core.YTIdType ty a' a')
elaborate (YTW a b) [] = match do
  (b', Core.YTType lb) <- scope a (elaborate b [] Nothing)
  (a', Core.YTType la) <- elaborate a [] Nothing
  return (Core.YTW a' b', Core.YTType (Level.ofW la lb))
elaborate YTTree {} [] = Prelude.error "TODO: YTTree inference"
-- Application mode propagation
elaborate (f :@: t) args = elaborate f (Arg t : args)
elaborate (YTFst p) args = elaborate p (AFst : args)
elaborate (YTSnd p) args = elaborate p (ASnd : args)
elaborate (YTIf g b t e) args = elaborate b (AIf g t e : args)
elaborate (YTJ g e r) args = elaborate e (AJ g r : args)
elaborate (YTRec g e s) args = elaborate e (ARec g s : args)
-- Application mode resolution
elaborate (YTAbs a f) (Arg x : args) = \ty -> do
  -- TODO: pass values to context as @ty@ might depend on @x@ here
  (f', ft) <- scope a $ elaborate f (shift args) (Free.lift <$> ty)
  (x', a') <- elaborate x [] (Just a)
  return (Core.YTAbs a' f' Core.:@: x', ft @ x')
-- TODO: do not ignore @b@ here
elaborate (YTPair _ f _) (AFst : args) = elaborate f args
-- TODO: do not ignore @b@ here
elaborate (YTPair _ _ s) (ASnd : args) = elaborate s args
-- TODO: do not ignore @g@ here
elaborate (YTBValue condition) (AIf _ t e : args)
  | condition = elaborate t args
  | otherwise = elaborate e args
-- TODO: do not ignore @g@ here
elaborate (YTRefl x) (AJ _ e : args) = elaborate (e @ x) args
elaborate YTTree {} (ARec _ _ : _) = Prelude.error "TODO: YTTree application resolution"
elaborate (Var v) args = \ty -> do
  ctxTy <- asks ($ v)
  apply (Core.Var v) ctxTy args ty
-- Metavar solving
elaborate MetaVar {} _ = Prelude.error "TODO: Metavar solving"
-- Mode switch
elaborate (tm :!: ty) args = match do
  (tm', ty') <- elaborate tm [] (Just ty)
  apply tm' (bubble ty') args Nothing
-- If nothing suffices, fail.
elaborate _ _ = \_ -> Monad.fail ""
