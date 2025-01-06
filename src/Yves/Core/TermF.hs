module Yves.Core.TermF where

import Data.Bool (Bool)
import Numeric.Natural (Natural)

type Level = Natural

data TermF s t
  = TypeF {tfLevel :: !Level}
  | PiF {pfAlpha :: t, pfBeta :: s}
  | AbsF {absFAlpha :: t, absFBody :: s}
  | AppF {appfFun, appfArg :: t}
  | SigmaF {sfAlpha :: t, sfBeta :: s}
  | PairF {pfBeta :: s, pfFst, pfSnd :: t}
  | FstF {ffPair :: t}
  | SndF {sfPair :: t}
  | BoolTypeF
  | BoolValF {bvfValue :: !Bool}
  | IfF {ifGamma :: s, ifCond, ifThen, ifElse :: t}
  | IdTypeF {itfAlpha, itfLeft, itfRight :: t}
  | ReflF {rfPoint :: t}
  | JF {jfGamma :: s, jfElim :: t, jfTrans :: s}
  | WF {wfAlpha :: t, wfBeta :: s}
  | TreeF {tfBeta :: s, tfRoot, tfSubtr :: t}
  | WRecF {wrfGamma :: s, wrfElim :: t, wrfStep :: s}
