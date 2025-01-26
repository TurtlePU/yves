{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}

module Yves.TermF where

import Data.Bifunctor.Sum (Sum)
import Data.Bifunctor.TH qualified as TH
import Data.Functor (Functor)
import Yves.Core.TermF qualified as Core

data SurfaceF m s t
  = AscrF {afTerm, afType :: t}
  | MetaVarF {mvfVar :: m, mvfArgs :: [t]}
  deriving (Functor)

$(TH.deriveBifunctor ''SurfaceF)
$(TH.deriveBifoldable ''SurfaceF)
$(TH.deriveBitraversable ''SurfaceF)

type TermF m = Sum Core.TermF (SurfaceF m)
