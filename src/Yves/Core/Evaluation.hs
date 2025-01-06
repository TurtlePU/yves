module Yves.Core.Evaluation where

import Control.Monad.Scoped.Free qualified as Free
import Control.Monad.Scoped.Free.In (In)
import Yves.Core.YTerm
import Prelude qualified

evaluate :: YTerm v -> YTerm v
evaluate = Free.teardown Var evaluateF

evaluateF :: TermF (YTerm (In v)) (YTerm v) -> YTerm v
evaluateF = Prelude.error "TODO"
