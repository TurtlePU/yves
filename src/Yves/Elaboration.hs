{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeOperators #-}

module Yves.Elaboration where

import Control.Applicative (Alternative, Applicative (..))
import Control.Monad (Monad (..))
import Control.Monad qualified as Monad
import Control.Monad.Fail (MonadFail)
import Control.Monad.Reader (ReaderT (..))
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
import Data.Function ((.))
import Data.Functor (Functor (..), (<$>))
import Data.Functor.Identity (Identity (..))
import Data.Maybe (Maybe (..))
import Data.Traversable (Traversable (..))
import Yves.Core.Level qualified as Level
import Yves.Core.YTerm qualified as Core
import Yves.YTerm

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

data CtxEntry m v = Maybe (YTerm m v) :? YType m v
  deriving (Functor)

type Ctx m v = v -> CtxEntry m v

extend :: CtxEntry m v -> Ctx m v -> Ctx m (In v)
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
    (Applicative, Alternative, Monad, MonadFail, MonadState (Sub s m v))
    via (ReaderT (Ctx m v) (MaybeT (State (Sub s m v))))

scope :: (Collection s) => CtxEntry m v -> Elab s m (In v) a -> Elab s m v a
scope en = Elab . (. extend en) . (scopeState .) . elab

data Arg m v
  = Arg (YTerm m v)
  | AFst
  | ASnd
  | AJ (YType m v) (YTerm m (In v))

shift :: [Arg m v] -> [Arg m (In v)]
shift = fmap impl
  where
    impl :: Arg m v -> Arg m (In v)
    impl (Arg t) = Arg (Free.lift t)
    impl AFst = AFst
    impl ASnd = ASnd
    impl (AJ ty tm) = AJ (Free.lift ty) (fmap (fmap In.There) tm)

solve :: YType m v -> [Arg m v] -> Core.YType v -> Elab s m v ()
solve = _

bubble :: Core.YTerm v -> YTerm m v
bubble = Free.teardown Var (Free.FTerm . Sum.L2)

elaborate ::
  (Collection s, Key s ~ m, Eq v) =>
  YTerm m v ->
  [Arg m v] ->
  Maybe (Core.YType v) ->
  Elab s m v (Core.YTerm v, Core.YType v)
elaborate (Var v) args ty = _
elaborate (MetaVar v) args ty = _
elaborate (YTType l) [] Nothing =
  return (Core.YTType l, Core.YTType (Level.ofType l))
elaborate (a :~>: b) [] Nothing = do
  (a', Core.YTType la) <- elaborate a [] Nothing
  (b', Core.YTType lb) <- scope (Nothing :? bubble a') (elaborate b [] Nothing)
  return (a' Core.:~>: b', Core.YTType (Level.ofPi la lb))
elaborate (YTAbs a f) [] (Just ty@(a' Core.:~>: b)) = do
  solve a [] a'
  (f', _) <- scope (Nothing :? bubble a') (elaborate f [] (Just b))
  return (Core.YTAbs a' f', ty)
elaborate (YTAbs a f) (Arg x : args) ty = do
  (f', ft) <- scope (Just x :? a) (elaborate f (shift args) (Free.lift <$> ty))
  (a', Core.YTType _) <- elaborate a [] Nothing
  return (Core.YTAbs a' f', a' Core.:~>: ft)
elaborate (f :@: t) args ty = do
  (f', a Core.:~>: b) <- elaborate f (Arg t : args) ty
  (t', _) <- elaborate t [] (Just a)
  return (f' Core.:@: t', b @ t')
elaborate (a :*: b) [] Nothing = do
  (a', Core.YTType la) <- elaborate a [] Nothing
  (b', Core.YTType lb) <- scope (Nothing :? bubble a') (elaborate b [] Nothing)
  return (a' Core.:*: b', Core.YTType (Level.ofSigma la lb))
elaborate (YTPair b f s) [] (Just ty@(a Core.:*: b')) = do
  (f', _) <- elaborate f [] (Just a)
  (s', _) <- elaborate s [] (Just (b' @ f'))
  scope (Just f :? bubble a) (solve b [] b')
  return (Core.YTPair b' f' s', ty)
elaborate (YTPair _ f s) (AFst : args) ty = do
  (f', a) <- elaborate f args ty
  (s', b0) <- elaborate s [] Nothing
  let b = Free.lift b0
  return (Core.YTPair b f' s', a Core.:*: b)
elaborate (YTPair _ f s) (ASnd : args) ty = do
  (s', b0) <- elaborate s args ty
  (f', a) <- elaborate f [] Nothing
  let b = Free.lift b0
  return (Core.YTPair b f' s', a Core.:*: b)
elaborate (YTFst p) args ty = do
  (p', a Core.:*: _) <- elaborate p (AFst : args) ty
  return (Core.YTFst p', a)
elaborate (YTSnd p) args ty = do
  (p', _ Core.:*: b) <- elaborate p (ASnd : args) ty
  return (Core.YTSnd p', b @ Core.YTFst p')
elaborate YTBool [] Nothing = return (Core.YTBool, Core.YTType Level.ofBool)
elaborate (YTBValue b) [] (Just ty@Core.YTBool) = return (Core.YTBValue b, ty)
elaborate (YTIf g b t e) args ty = _
elaborate (YTIdType a x y) [] Nothing = do
  (a', Core.YTType l) <- elaborate a [] Nothing
  (x', _) <- elaborate x [] (Just a')
  (y', _) <- elaborate y [] (Just a')
  return (Core.YTIdType a' x' y', Core.YTType (Level.ofId l))
elaborate (YTRefl x) [] (Just (Core.YTIdType a l r)) = _
elaborate (YTRefl x) (AJ g e : args) ty = _
elaborate (YTJ g e r) args ty = do
  (e', Core.YTIdType a _ _) <- elaborate e (AJ g r : args) ty
  (g', _) <- elaborate g [] Nothing
  (r', _) <- scope (Nothing :? bubble a) (elaborate r [] _)
  return (Core.YTJ g' e' r', _)
elaborate (YTW a b) [] Nothing = do
  (a', Core.YTType la) <- elaborate a [] Nothing
  (b', Core.YTType lb) <- scope (Nothing :? bubble a') (elaborate b [] Nothing)
  return (Core.YTW a' b', Core.YTType (Level.ofW la lb))
elaborate (YTTree b r s) args ty = _
elaborate (YTRec g e s) args ty = _
elaborate (tm :!: as) args ty = _
elaborate tm args (Just ty) = do
  (tm', ty') <- elaborate tm args Nothing
  solve (bubble ty') args ty
  return (tm', ty')
elaborate _ _ Nothing = Monad.fail ""
