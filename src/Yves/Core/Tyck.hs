{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}

module Yves.Core.Tyck where

import Control.Applicative (Applicative (..))
import Control.Monad (Monad (..))
import Control.Monad qualified as Monad
import Control.Monad.Scoped.Free (Free)
import Control.Monad.Scoped.Free qualified as Free
import Data.Bool (Bool)
import Data.Bool qualified as Bool
import Data.Function (($), (.))
import Data.Functor (Functor (..), (<$>))
import Data.Maybe (Maybe)
import Data.Maybe qualified as Maybe
import Data.Traversable (Traversable (..))
import Yves.Core.Level (Level)
import Yves.Core.Level qualified as Level
import Yves.Core.TermF (TermF (..))
import Prelude qualified

type YTerm = Free TermF

infix 9 @

(@) :: YTerm (Maybe v) -> YTerm v -> YTerm v
f @ t = f >>= Maybe.maybe t pure

pattern YTType :: Level -> YTerm v
pattern YTType l = Free.FTerm (TypeF l)

infixr 5 :~>:

pattern (:~>:) :: YTerm v -> YTerm (Maybe v) -> YTerm v
pattern a :~>: b = Free.FTerm (PiF a b)

pattern (:@:) :: YTerm v -> YTerm v -> YTerm v
pattern f :@: t = Free.FTerm (AppF f t)

infixr 6 :*:

pattern (:*:) :: YTerm v -> YTerm (Maybe v) -> YTerm v
pattern a :*: b = Free.FTerm (SigmaF a b)

pattern YTPair :: YTerm (Maybe v) -> YTerm v -> YTerm v -> YTerm v
pattern YTPair b f s = Free.FTerm (PairF b f s)

pattern YTFst :: YTerm v -> YTerm v
pattern YTFst p = Free.FTerm (FstF p)

pattern YTBool :: YTerm v
pattern YTBool = Free.FTerm BoolTypeF

pattern YTBValue :: Bool -> YTerm v
pattern YTBValue b = Free.FTerm (BoolValF b)

pattern YTIdType :: YTerm v -> YTerm v -> YTerm v -> YTerm v
pattern YTIdType t l r = Free.FTerm (IdTypeF t l r)

pattern YTRefl :: YTerm v -> YTerm v
pattern YTRefl p = Free.FTerm (ReflF p)

pattern YTW :: YTerm v -> YTerm (Maybe v) -> YTerm v
pattern YTW a b = Free.FTerm (WF a b)

pattern YTTree :: YTerm (Maybe v) -> YTerm v -> YTerm v -> YTerm v
pattern YTTree b r s = Free.FTerm (TreeF b r s)

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
(<:) = Prelude.error "TODO"

synthesizeF ::
  TermF (YTerm (Maybe v), YType v -> Maybe (YType (Maybe v))) (YTerm v, YType v) ->
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
        extType = fmap there alpha :*: ctxEqType
        -- x: a, y: a |- x = y
        ctxEqType =
          YTIdType
            (there . there <$> alpha)
            (var $ there here)
            (var here)
    -- s: (x: a) * (y: a) * (x = y) |- G: Type
    YTType _ <- typeOf jfGamma $ alpha :*: extType
    let gamma = valueOf jfGamma
        -- _: _, x: a |- (y: a) * (x = y)
        extType' =
          extType >>= \case
            Maybe.Nothing -> var here
            Maybe.Just v -> var (there (there v))
        -- x: a |- G[s:=(x,(x,refl))]
        x = var here
        onReflType =
          gamma >>= \case
            Maybe.Nothing -> YTPair extType' x $ YTPair ctxEqType x $ YTRefl x
            Maybe.Just v -> var (there v)
        -- y: a |- left = y
        onLeftType = YTIdType (there <$> alpha) (there <$> left) (var here)
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
    subtrType <- sequence subtrType0
    Monad.guard (subtrType <: retType)
    return retType
  WRecF {..} -> do
    w@(YTW alpha beta) <- pure (typeOf wrfElim)
    let gamma = valueOf wrfGamma
    YTType _ <- typeOf wrfGamma w
    let -- (root: a) * (subt: B(root) -> W) * ((arg: B(root)) -> G(subt(arg)))
        stepArgType = alpha :*: subtrAndHypType
        -- root: a |- (subt: B(root) -> W) * ((arg: B(root)) -> G(subt(arg)))
        subtrAndHypType = (beta :~>: fmap (there . there) w) :*: indHypType
        -- root: a, subt: B(root) -> W |- (arg: B(root)) -> G(subt(arg))
        indHypType = fmap there beta :~>: gammaSA
        -- root: a, subt: B(root) -> W, arg: B(root) |- G(subt(arg))
        gammaSA =
          gamma >>= \case
            Maybe.Nothing -> var (there here) :@: var here
            Maybe.Just v -> var . there $ there (there v)
    -- should be
    -- s: stepArgType |- G(tree(B, fst s, fst (snd s)))
    -- in fact is
    -- s: stepArgType |- H(s)
    stepType0 <- typeOf wrfStep stepArgType
    let -- _: _, _: _, _: _, root: a |- (subt: B(root) -> W) * ((arg: B(root)) -> G(subt(arg)))
        sahType''' =
          subtrAndHypType >>= \case
            Maybe.Nothing -> var here
            Maybe.Just v -> var . there . there $ there (there v)
        -- root: a, _: _, _: _, subt: B(root) -> W |- (arg: B(root)) -> G(subt(arg))
        hypType'' =
          indHypType >>= \case
            Maybe.Nothing -> var here
            Maybe.Just Maybe.Nothing -> var . there $ there (there here)
            Maybe.Just (Maybe.Just v) -> var . there . there $ there (there v)
        -- should be
        -- root: a, subt: B(root) -> W, _: _ |- G(tree(B, root, subst))
        -- in fact is
        -- root: a, subt: B(root) -> W, hyp: hypType'' |- H(root,(subt,hyp))
        stepType''' =
          stepType0 >>= \case
            Maybe.Nothing ->
              YTPair sahType''' (var . there $ there here) $
                YTPair hypType'' (var $ there here) (var here)
            Maybe.Just v -> var . there $ there (there v)
        -- _: _, _: _, root: a |- B: Type
        beta'' =
          beta >>= \case
            Maybe.Nothing -> var here
            Maybe.Just v -> var . there $ there (there v)
        -- root: a, subt: B(root) -> W |- G(tree(B, root, subt))
        gamma' =
          gamma >>= \case
            Maybe.Nothing -> YTTree beta'' (var $ there here) (var here)
            Maybe.Just v -> var $ there (there v)
    -- root: a, subt: B(root) -> W |- ???
    stepType <- sequence stepType'''
    Monad.guard (stepType <: gamma')
    return (gamma @ valueOf wrfElim)
