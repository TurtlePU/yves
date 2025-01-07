{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Yves.Core.Synthesis (synthesizeF) where

import Control.Applicative (Applicative (..))
import Control.Monad (Monad (..))
import Control.Monad qualified as Monad
import Control.Monad.Scoped.Free ((@))
import Control.Monad.Scoped.Free.In (In (..))
import Control.Monad.Scoped.Free.In qualified as In
import Data.Bool qualified as Bool
import Data.Eq (Eq)
import Data.Function (($), (.))
import Data.Functor (Functor (..), (<$>))
import Data.Maybe (Maybe)
import Data.Traversable (Traversable (..))
import Yves.Core.Level qualified as Level
import Yves.Core.Subtyping ((<:))
import Yves.Core.YTerm

typeOf :: (a, b) -> b
typeOf (_, t) = t

valueOf :: (a, b) -> a
valueOf (v, _) = v

synthesizeF ::
  (Eq v) =>
  TermF (YTerm (In v), YType v -> Maybe (YType (In v))) (YTerm v, YType v) ->
  Maybe (YType v)
synthesizeF = \case
  TypeF l -> pure $ YTType (Level.succ l)
  PiF {..} -> do
    YTType l <- pure (typeOf pfAlpha)
    YTType l' <- typeOf pfBeta (valueOf pfAlpha)
    return $ YTType (l `Level.max` l')
  AbsF {..} -> do
    YTType _ <- pure (typeOf absFAlpha)
    let alpha = valueOf absFAlpha
    beta <- typeOf absFBody alpha
    return (alpha :~>: beta)
  AppF {..} -> do
    alpha :~>: beta <- pure (typeOf appfFun)
    let argType = typeOf appfArg
    Monad.guard (argType <: alpha)
    return (beta @ valueOf appfArg)
  SigmaF {..} -> do
    YTType l <- pure (typeOf sfAlpha)
    YTType l' <- typeOf sfBeta (valueOf sfAlpha)
    return $ YTType (l `Level.max` l')
  PairF {..} -> do
    let alpha = typeOf pfFst
    YTType _ <- typeOf pfBeta alpha
    let beta = valueOf pfBeta
        sndType = typeOf pfSnd
    Monad.guard (sndType <: beta @ valueOf pfFst)
    return (alpha :*: beta)
  FstF p -> do
    alpha :*: _ <- pure (typeOf p)
    return alpha
  SndF p -> do
    _ :*: beta <- pure (typeOf p)
    return $ beta @ YTFst (valueOf p)
  BoolTypeF -> pure (YTType 1)
  BoolValF _ -> pure YTBool
  IfF {..} -> do
    YTBool <- pure (typeOf ifCond)
    YTType _ <- typeOf ifGamma YTBool
    let gamma = valueOf ifGamma
    Monad.guard (typeOf ifThen <: gamma @ YTBValue Bool.True)
    Monad.guard (typeOf ifElse <: gamma @ YTBValue Bool.False)
    return (gamma @ valueOf ifCond)
  IdTypeF {..} -> do
    YTType _ <- pure (typeOf itfAlpha)
    let alpha = valueOf itfAlpha
    Monad.guard (typeOf itfLeft <: alpha)
    Monad.guard (typeOf itfRight <: alpha)
    return (YTType 0)
  ReflF p -> let v = valueOf p in pure $ YTIdType (typeOf p) v v
  JF {..} -> do
    YTIdType alpha left right <- pure (typeOf jfElim)
    transType <- typeOf jfTrans alpha
    let -- x: a |- (y: a) * (x = y)
        extType = fmap There alpha :*: ctxEqType
        -- x: a, y: a |- x = y
        ctxEqType =
          YTIdType
            (There . There <$> alpha)
            (Var $ There Here)
            (Var Here)
    -- s: (x: a) * (y: a) * (x = y) |- G: Type
    YTType _ <- typeOf jfGamma $ alpha :*: extType
    let gamma = valueOf jfGamma
        -- _: _, x: a |- (y: a) * (x = y)
        extType' =
          extType >>= \case
            Here -> Var Here
            There v -> Var (There (There v))
        -- x: a |- G[s:=(x,(x,refl))]
        x = Var Here
        onReflType =
          gamma >>= \case
            Here -> YTPair extType' x $ YTPair ctxEqType x $ YTRefl x
            There v -> Var (There v)
        -- y: a |- left = y
        onLeftType = YTIdType (There <$> alpha) (There <$> left) (Var Here)
        -- (left,(right,elim))
        gammaArg =
          YTPair extType left $ YTPair onLeftType right (valueOf jfElim)
    Monad.guard (transType <: onReflType)
    return $ gamma @ gammaArg
  WF {..} -> do
    YTType l <- pure (typeOf wfAlpha)
    YTType l' <- typeOf wfBeta (valueOf wfAlpha)
    return $ YTType (l `Level.max` l')
  TreeF {..} -> do
    let alpha = typeOf tfRoot
    YTType _ <- typeOf tfBeta alpha
    let beta = valueOf tfBeta
        retType = YTW alpha beta
    -- tfSubtr : B(root) -> W
    (betaAtRoot :~>: subtrType0) <- pure (typeOf tfSubtr)
    Monad.guard (beta @ valueOf tfRoot <: betaAtRoot)
    subtrType <- traverse In.toMaybe subtrType0
    Monad.guard (subtrType <: retType)
    return retType
  WRecF {..} -> do
    w@(YTW alpha beta) <- pure (typeOf wrfElim)
    let gamma = valueOf wrfGamma
    YTType _ <- typeOf wrfGamma w
    let -- (root: a) * (subt: B(root) -> W) * ((arg: B(root)) -> G(subt(arg)))
        stepArgType = alpha :*: subtrAndHypType
        -- root: a |- (subt: B(root) -> W) * ((arg: B(root)) -> G(subt(arg)))
        subtrAndHypType = (beta :~>: fmap (There . There) w) :*: indHypType
        -- root: a, subt: B(root) -> W |- (arg: B(root)) -> G(subt(arg))
        indHypType = fmap There beta :~>: gammaSA
        -- root: a, subt: B(root) -> W, arg: B(root) |- G(subt(arg))
        gammaSA =
          gamma >>= \case
            Here -> Var (There Here) :@: Var Here
            There v -> Var . There $ There (There v)
    -- should be
    -- s: stepArgType |- G(tree(B, fst s, fst (snd s)))
    -- in fact is
    -- s: stepArgType |- H(s)
    stepType0 <- typeOf wrfStep stepArgType
    let -- _: _, _: _, _: _, root: a |-
        -- (subt: B(root) -> W) * ((arg: B(root)) -> G(subt(arg)))
        sahType''' =
          subtrAndHypType >>= \case
            Here -> Var Here
            There v -> Var . There . There $ There (There v)
        -- root: a, _: _, _: _, subt: B(root) -> W |-
        -- (arg: B(root)) -> G(subt(arg))
        hypType'' =
          indHypType >>= \case
            Here -> Var Here
            There v -> Var . There $ There (There v)
        -- should be
        -- root: a, subt: B(root) -> W, _: _ |- G(tree(B, root, subst))
        -- in fact is
        -- root: a, subt: B(root) -> W, hyp: hypType'' |- H(root,(subt,hyp))
        stepType''' =
          stepType0 >>= \case
            Here ->
              YTPair sahType''' (Var . There $ There Here) $
                YTPair hypType'' (Var $ There Here) (Var Here)
            There v -> Var . There $ There (There v)
        -- _: _, _: _, root: a |- B: Type
        beta'' =
          beta >>= \case
            Here -> Var Here
            There v -> Var . There $ There (There v)
        -- root: a, subt: B(root) -> W |- G(tree(B, root, subt))
        gamma' =
          gamma >>= \case
            Here -> YTTree beta'' (Var $ There Here) (Var Here)
            There v -> Var $ There (There v)
    -- root: a, subt: B(root) -> W |- ???
    stepType <- traverse In.toMaybe stepType'''
    Monad.guard (stepType <: gamma')
    return (gamma @ valueOf wrfElim)
