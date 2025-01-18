{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeOperators #-}

module Yves.Elaboration where

import Control.Applicative (Alternative, Applicative)
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
import Data.Function (($), (.))
import Data.Functor (Functor (..))
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
  | ALeft
  | ARight
  | AJ (YType m v) (YTerm m (In v))

shift :: [Arg m v] -> [Arg m (In v)]
shift = fmap impl
  where
    impl :: Arg m v -> Arg m (In v)
    impl (Arg t) = Arg (Free.lift t)
    impl ALeft = ALeft
    impl ARight = ARight
    impl (AJ ty tm) = AJ (Free.lift ty) (fmap (fmap In.There) tm)

solve :: YType m v -> [Arg m v] -> Core.YType v -> Elab s m v ()
solve = _

bubble :: Core.YTerm v -> YTerm m v
bubble = Free.teardown Var (Free.FTerm . Sum.L2)

elaborate ::
  (Collection s, Key s ~ m) =>
  YTerm m v ->
  [Arg m v] ->
  Core.YType v ->
  Elab s m v (Core.YTerm v, Core.YType v)
elaborate (Var v) args ty = _
elaborate (MetaVar v) args ty = _
elaborate (YTType l) [] ty@(Core.YTType l') = do
  Monad.guard (Level.ofType l == l')
  return (Core.YTType l, ty)
elaborate (a :~>: b) [] ty@(Core.YTType l) = do
  (a', _) <- elaborate a [] ty
  (b', _) <- scope (Nothing :? bubble a') (elaborate b [] (Core.YTType l))
  return (a' Core.:~>: b', ty)
elaborate (YTAbs a f) [] ty@(a' Core.:~>: b) = do
  solve a [] a'
  (f', _) <- scope (Nothing :? bubble a') (elaborate f [] b)
  return (Core.YTAbs a' f', ty)
elaborate (YTAbs a f) (Arg x : args) ty = do
  (f', ft) <- scope (Just x :? a) (elaborate f (shift args) (Free.lift ty))
  YTType l <- infer a
  (a', _) <- elaborate a [] (Core.YTType l)
  return (Core.YTAbs a' f', a' Core.:~>: ft)
elaborate (f :@: t) args ty = do
  (f', a Core.:~>: b) <- elaborate f (Arg t : args) ty
  (t', _) <- elaborate t [] a
  return (f' Core.:@: t', b @ t')
elaborate (a :*: b) [] ty@(Core.YTType l) = do
  (a', _) <- elaborate a [] ty
  (b', _) <- scope (Nothing :? bubble a') (elaborate b [] (Core.YTType l))
  return (a' Core.:*: b', ty)
elaborate (YTPair b f s) [] ty@(a Core.:*: b') = do
  (f', _) <- elaborate f [] a
  (s', _) <- elaborate s [] (b' @ f')
  scope (Just f :? bubble a) (solve b [] b')
  return (Core.YTPair b' f' s', ty)
elaborate (YTPair _ f s) (ALeft : args) ty = do
  (f', a) <- elaborate f args ty
  b0 <- infer s
  YTType l <- infer b0
  (b', _) <- elaborate b0 [] (Core.YTType l)
  (s', _) <- elaborate s [] b'
  let b = Free.lift b'
  return (Core.YTPair b f' s', a Core.:*: b)
elaborate (YTPair _ f s) (ARight : args) ty = do
  (s', b0) <- elaborate s args ty
  let b = Free.lift b0
  a0 <- infer f
  YTType l <- infer a0
  (a, _) <- elaborate a0 [] (Core.YTType l)
  (f', _) <- elaborate f [] a
  return (Core.YTPair b f' s', a Core.:*: b)
elaborate (YTFst p) args ty = do
  (p', a Core.:*: _) <- elaborate p (ALeft : args) ty
  return (Core.YTFst p', a)
elaborate (YTSnd p) args ty = do
  (p', _ Core.:*: b) <- elaborate p (ARight : args) ty
  return (Core.YTSnd p', b @ Core.YTFst p')
elaborate YTBool [] ty@(Core.YTType l) = do
  Monad.guard (Level.ofBool == l)
  return (Core.YTBool, ty)
elaborate (YTBValue b) [] ty@Core.YTBool = return (Core.YTBValue b, ty)
elaborate (YTIdType a x y) [] ty@(Core.YTType l) = do
  (a', _) <- elaborate a [] $ Core.YTType (Level.perId l)
  (x', _) <- elaborate x [] a'
  (y', _) <- elaborate y [] a'
  return (Core.YTIdType a' x' y', ty)
elaborate (YTRefl x) [] (Core.YTIdType a l r) = _
elaborate (YTRefl x) (AJ g e : args) ty = _
elaborate (YTJ g e r) args ty = do
  (e', Core.YTIdType a x y) <- elaborate e (AJ g r : args) ty
  return (Core.YTJ _ e' _, _)
elaborate _ _ _ = Monad.fail ""

infer :: YTerm m v -> Elab s m v (YTerm m v)
infer = _
