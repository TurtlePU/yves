module Yves.Core.TermF where

import Data.Bool (Bool)
import Numeric.Natural (Natural)

type Level = Natural

data TermF s t
  = TypeF {tfLevel :: !Level}
  | PiF {pfAlpha :: t, pfBeta :: s}
  | AbsF {absFAlpha :: t, absFBody :: s}
  | AppF {appfFun :: t, appfArg :: t}
  | SigmaF {sfAlpha :: t, sfBeta :: s}
  | PairF {pfBeta :: s, pfFst :: t, pfSnd :: t}
  | FstF {ffPair :: t}
  | SndF {sfPair :: t}
  | WF {wfAlpha :: t, wfBeta :: s}
  | TreeF {tfBeta :: s, tfRoot :: t, tfSubtr :: s}
  | WRecF {wrfGamma :: s, wrfElim :: t, wrfStep :: s}
  | BoolTypeF
  | BoolValF {bvfValue :: !Bool}
  | IfF {ifGamma :: s, ifCond :: t, ifThen :: t, ifElse :: t}
