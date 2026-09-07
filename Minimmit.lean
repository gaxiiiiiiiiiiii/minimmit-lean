import Minimmit.Model.Transition.Basic
import Minimmit.Model.Transition.Execute
import Minimmit.Model.Certificate.Basic
import Minimmit.Model.Certificate.Mono
import Minimmit.Model.Algo.Basic
import Minimmit.Model.Algo.Disseminate
import Minimmit.Model.Algo.Stage
import Minimmit.Model.Algo.LocalInv
import Minimmit.Model.Algo.Climb
import Minimmit.Model.Algo.Send
import Minimmit.Model.Algo.Forward
import Minimmit.Model.Constraint.Basic
import Minimmit.Model.Constraint.Run
import Minimmit.Model.Constraint.Witness
import Minimmit.Analysis.Consistency.Lemma5_1
import Minimmit.Analysis.Consistency.Lemma5_2
import Minimmit.Analysis.Consistency.Lemma5_3
import Minimmit.Analysis.Consistency.Lemma5_4
import Minimmit.Analysis.Liveness.Timing
import Minimmit.Analysis.Liveness.Lemma5_5
import Minimmit.Analysis.Liveness.LeaderRound
import Minimmit.Analysis.Liveness.Lemma5_6
import Minimmit.Analysis.Liveness.Lemma5_7
import Minimmit.Analysis.Liveness.Finalise
import Minimmit.Analysis.Log
import Minimmit.Analysis.Responsiveness.Lemma5_8
import Minimmit.Analysis.Responsiveness.Lemma5_9
import Minimmit.Analysis.Responsiveness.Lemma5_10
import Minimmit.Axioms

/-!
# Minimmit の形式化

論文 arXiv:2508.10862 に基づく。`Model/` が §4（定義と、モデルについての補題）、`Analysis/` が
§5（Lemma 5.1〜5.10）。`Model/` の各ディレクトリでは `Basic.lean` が定義で、他のファイルは補題。
-/
