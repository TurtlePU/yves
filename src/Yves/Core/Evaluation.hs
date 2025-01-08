{-# LANGUAGE LambdaCase #-}

module Yves.Core.Evaluation where

import Control.Monad (Monad (..))
import Control.Monad.Scoped.Free ((@))
import Control.Monad.Scoped.Free qualified as Free
import Control.Monad.Scoped.Free.In (In (..))
import Control.Monad.Scoped.Free.In qualified as In
import Data.Function (($), (.))
import Data.Functor (Functor (..), (<$>))
import Yves.Core.YTerm

evaluate :: YTerm v -> YTerm v
evaluate = Free.teardown Var evaluateF

evaluateF :: TermF (YTerm (In v)) (YTerm v) -> YTerm v
evaluateF = \case
  AppF (YTAbs _ f) t -> evaluate (f @ t)
  FstF (YTPair _ fst _) -> fst
  SndF (YTPair _ _ snd) -> snd
  IfF _ (YTBValue b) thenB elseB -> if b then thenB else elseB
  JF _ (YTRefl x) t -> evaluate (t @ x)
  WRecF gamma (YTTree beta root subtr) rec@(YTAbs _ (YTAbs _ (YTAbs _ step))) ->
    let stepArg =
          YTAbs (beta @ root) $
            YTWRec
              (In.elim Here (There . There) <$> gamma)
              (fmap There subtr :@: Var Here)
              (There <$> rec)
     in evaluate $
          step >>= \case
            Here -> stepArg
            There Here -> subtr
            There (There Here) -> root
            There (There (There v)) -> Var v
  t -> Free.FTerm t
