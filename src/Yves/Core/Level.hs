module Yves.Core.Level where

import Data.Function qualified as Function
import Data.Ord qualified as Ord
import Numeric.Natural (Natural)
import Prelude qualified

type Level = Natural

ofType, ofId :: Level -> Level
ofType = Prelude.succ
ofId = Function.id

ofPi, ofSigma, ofW :: Level -> Level -> Level
ofPi = Ord.max
ofSigma = Ord.max
ofW = Ord.max

ofBool :: Level
ofBool = 1
