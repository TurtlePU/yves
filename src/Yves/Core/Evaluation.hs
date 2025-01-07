{-# LANGUAGE LambdaCase #-}

module Yves.Core.Evaluation where

import Control.Monad (Monad (..))
import Control.Monad.Scoped.Free ((@))
import Control.Monad.Scoped.Free qualified as Free
import Control.Monad.Scoped.Free.In (In (..))
import Data.Function (($), (.))
import Data.Functor (Functor (..), (<$>))
import Yves.Core.YTerm
import Prelude qualified

evaluate :: YTerm v -> YTerm v
evaluate = Free.teardown Var evaluateF

evaluateF :: TermF (YTerm (In v)) (YTerm v) -> YTerm v
evaluateF = \case
  AppF (YTAbs _ f) t -> evaluate (f @ t)
  FstF (YTPair _ fst _) -> fst
  SndF (YTPair _ _ snd) -> snd
  IfF _ (YTBValue b) thenB elseB -> if b then thenB else elseB
  JF _ (YTRefl x) t -> evaluate (t @ x)
  WRecF gamma (YTTree beta root subtr) step ->
    let wtf = Prelude.error "alpha is unknown here"
        up Here = Here
        up v = There v
        -- root: a |- (subtr: B(root) -> W) * ((arg: B(root)) -> G(subtr(arg)))
        outerBeta =
          (beta :~>: YTW wtf (up . up <$> beta)) -- root: a |- B(root) -> W
            :*: (fmap There beta :~>: obGamma)
        -- root: a, subtr: B(root), arg: B(root) |- G(subtr(arg))
        obGamma =
          gamma >>= \case
            Here -> Var (There Here) :@: Var Here
            v -> Var (There (There v))
        -- subtr: B(root) -> W |- (arg: B(root)) -> G(subtr(arg))
        innerBeta = fmap There (beta @ root) :~>: ibGamma
        -- subtr: B(root) -> W, arg: B(root) |- G(subtr(arg))
        ibGamma =
          gamma >>= \case
            Here -> Var (There Here) :@: Var Here
            v -> Var (There v)
        -- ??? : (arg: B(root)) -> G(subtr(arg))
        subtrStep =
          YTAbs (beta @ root) $
            YTWRec
              (up <$> gamma) -- _: _, w: W |- G(w): Type
              (fmap There subtr :@: Var Here) -- arg: B(root) |- subtr(arg): W
              (up <$> step) -- _: _, x: Arg |- step(x): Result
        stepArg = YTPair outerBeta root $ YTPair innerBeta subtr subtrStep
     in evaluate (step @ stepArg)
  t -> Free.FTerm t
