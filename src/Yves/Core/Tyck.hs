{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}

module Yves.Core.Tyck where

import Control.Applicative (Applicative (..))
import Control.Monad (Monad (..))
import Control.Monad qualified as Monad
import Data.Bool (Bool)
import Data.Bool qualified as Bool
import Data.Foldable (Foldable)
import Data.Function (($), (.))
import Data.Functor (Functor (..))
import Data.Maybe (Maybe)
import Data.Maybe qualified as Maybe
import Data.Ord qualified as Ord
import Data.Traversable (Traversable (..))
import Yves.Core.TermF (Level, TermF (..))
import Prelude qualified as Enum

data YTerm v = YTVar v | YTTerm (TermF (YTerm (Maybe v)) (YTerm v))

instance Functor YTerm

instance Applicative YTerm

instance Monad YTerm

instance Foldable YTerm

instance Traversable YTerm

infix 9 @

(@) :: YTerm (Maybe v) -> YTerm v -> YTerm v
f @ t = f >>= Maybe.maybe t pure

pattern YTType :: Level -> YTerm v
pattern YTType l = YTTerm (TypeF l)

infixr 5 :~>:

pattern (:~>:) :: YTerm v -> YTerm (Maybe v) -> YTerm v
pattern a :~>: b = YTTerm (PiF a b)

pattern (:@:) :: YTerm v -> YTerm v -> YTerm v
pattern f :@: t = YTTerm (AppF f t)

infixr 6 :*:

pattern (:*:) :: YTerm v -> YTerm (Maybe v) -> YTerm v
pattern a :*: b = YTTerm (SigmaF a b)

pattern YTPair :: YTerm (Maybe v) -> YTerm v -> YTerm v -> YTerm v
pattern YTPair b f s = YTTerm (PairF b f s)

pattern YTFst :: YTerm v -> YTerm v
pattern YTFst p = YTTerm (FstF p)

pattern YTW :: YTerm v -> YTerm (Maybe v) -> YTerm v
pattern YTW a b = YTTerm (WF a b)

pattern YTTree :: YTerm (Maybe v) -> YTerm v -> YTerm v -> YTerm v
pattern YTTree b r s = YTTerm (TreeF b r s)

pattern YTBool :: YTerm v
pattern YTBool = YTTerm BoolTypeF

pattern YTBValue :: Bool -> YTerm v
pattern YTBValue b = YTTerm (BoolValF b)

type YType = YTerm

typeOf :: (a, b) -> b
typeOf (_, t) = t

valueOf :: (a, b) -> a
valueOf (v, _) = v

here :: Maybe v
here = Maybe.Nothing

there :: v -> Maybe v
there = Maybe.Just

var :: v -> YTerm v
var = pure

infix 4 <:

(<:) :: YType v -> YType v -> Bool
(<:) = _

synthesizeF ::
  TermF (YTerm (Maybe v), YType v -> Maybe (YType (Maybe v))) (YTerm v, YType v) ->
  Maybe (YType v)
synthesizeF = \case
  TypeF l -> pure $ YTType (Enum.succ l)
  PiF {..} -> do
    YTType l <- pure (typeOf pfAlpha)
    YTType l' <- typeOf pfBeta (valueOf pfAlpha)
    return $ YTType (l `Ord.max` l')
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
    return $ YTType (l `Ord.max` l')
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
  WF {..} -> do
    YTType l <- pure (typeOf wfAlpha)
    YTType l' <- typeOf wfBeta (valueOf wfAlpha)
    return $ YTType (l `Ord.max` l')
  TreeF {..} -> do
    let alpha = typeOf tfRoot
    YTType _ <- typeOf tfBeta alpha
    let beta = valueOf tfBeta
        retType = YTW alpha beta
    (betaAtRoot :~>: subtrType0) <- pure (typeOf tfSubtr)
    Monad.guard (beta @ valueOf tfRoot <: betaAtRoot)
    subtrType <- sequence subtrType0
    Monad.guard (subtrType <: retType)
    return retType
  WRecF {..} -> do
    w@(YTW alpha beta) <- pure (typeOf wrfElim)
    let gamma = valueOf wrfGamma
    YTType _ <- typeOf wrfGamma w
    let stepArgType = {- root: -} alpha :*: subtrAndHypType
        subtrAndHypType =
          ({-subt:-} beta {-(root)-} :~>: fmap (there . there) w) :*: indHypType
        indHypType =
          {-(arg:-} fmap there beta {-(root)) -> -}
            :~>: ( gamma >>= \case
                     Maybe.Nothing -> var (there here) :@: var here
                     -- \^ subt (arg)
                     Maybe.Just v -> var . there $ there (there v)
                 )
    stepType0 <- typeOf wrfStep stepArgType
    let sahType''' =
          subtrAndHypType >>= \case
            Maybe.Nothing -> var here
            Maybe.Just v -> var . there . there $ there (there v)
        hypType'' =
          indHypType >>= \case
            Maybe.Nothing -> var here
            Maybe.Just Maybe.Nothing -> var (there here)
            Maybe.Just (Maybe.Just v) -> var . there . there $ there (there v)
        stepType''' =
          stepType0 >>= \case
            Maybe.Nothing ->
              YTPair sahType''' (var . there $ there here) $
                YTPair hypType'' (var $ there here) (var here)
            Maybe.Just v -> var . there $ there (there v)
        beta'' =
          beta >>= \case
            Maybe.Nothing -> var here
            Maybe.Just v -> var . there $ there (there v)
        gamma' =
          gamma >>= \case
            Maybe.Nothing -> YTTree beta'' (var $ there here) (var here)
            Maybe.Just v -> var $ there (there v)
    stepType <- sequence stepType'''
    Monad.guard (stepType <: gamma')
    return (gamma @ valueOf wrfElim)
  BoolTypeF -> pure (YTType 1)
  BoolValF _ -> pure YTBool
  IfF {..} -> do
    YTBool <- pure (typeOf ifCond)
    YTType _ <- typeOf ifGamma YTBool
    let gamma = valueOf ifGamma
    Monad.guard (typeOf ifThen <: gamma @ YTBValue Bool.True)
    Monad.guard (typeOf ifElse <: gamma @ YTBValue Bool.False)
    return (gamma @ valueOf ifCond)
