{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Yves.Core.Synthesis (synthesizeF) where

import Control.Applicative (Applicative (..))
import Control.Monad (Monad (..), (<=<))
import Control.Monad qualified as Monad
import Control.Monad.Scoped.Free ((@))
import Control.Monad.Scoped.Free.In (In (..))
import Control.Monad.Scoped.Free.In qualified as In
import Data.Bool ((&&))
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
    a :~>: a0
      :~>: YTIdType a1 (Var (There Here)) (Var Here)
      :~>: YTType _ <-
      pure (typeOf jfGamma)
    a' <- traverse In.toMaybe a0
    a'' <- traverse (In.toMaybe <=< In.toMaybe) a1
    Monad.guard (alpha <: a && alpha <: a' && a <: a'' && a' <: a'')
    YTAbs _ (YTAbs _ (YTAbs _ gamma)) <- pure (valueOf jfGamma)
    let onReflType =
          gamma >>= \case
            Here -> YTRefl (Var Here)
            There Here -> Var Here
            There (There v) -> Var v
    Monad.guard (transType <: onReflType)
    return $
      gamma >>= \case
        Here -> valueOf jfElim
        There Here -> right
        There (There Here) -> left
        There (There (There v)) -> Var v
  WF {..} -> do
    YTType l <- pure (typeOf wfAlpha)
    YTType l' <- typeOf wfBeta (valueOf wfAlpha)
    return $ YTType (l `Level.max` l')
  TreeF {..} -> do
    let alpha = typeOf tfRoot
        beta = valueOf tfBeta
        retType = YTW alpha beta
    YTType _ <- typeOf tfBeta alpha
    -- tfSubtr : B(root) -> W
    (betaAtRoot :~>: subtrType0) <- pure (typeOf tfSubtr)
    Monad.guard (beta @ valueOf tfRoot <: betaAtRoot)
    subtrType <- traverse In.toMaybe subtrType0
    Monad.guard (subtrType <: retType)
    return retType
  WRecF {..} -> do
    w@(YTW alpha beta) <- pure (typeOf wrfElim)
    YTType _ <- typeOf wrfGamma w
    (a :~>: (br :~>: w0) :~>: (br0 :~>: ht) :~>: st) <- pure (typeOf wrfStep)
    w' <- traverse (In.toMaybe <=< In.toMaybe) w0
    br' <- traverse In.toMaybe br0
    let gamma = valueOf wrfGamma
        hypType =
          gamma >>= \case
            Here -> Var (There Here) :@: Var Here
            v -> Var $ There (There v)
        stepType =
          gamma >>= \case
            Here ->
              YTTree
                (In.elim Here (There . There . There) <$> beta)
                (Var $ There Here)
                $ Var Here
            v -> Var (There v)
    Monad.guard (alpha <: a && br <: beta && w <: w' && br' <: beta)
    Monad.guard (hypType <: ht && st <: fmap There stepType)
    return (gamma @ valueOf wrfElim)
