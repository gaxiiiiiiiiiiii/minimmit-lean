import Minimmit.Model.Transition
import Minimmit.Model.Certificate
import Minimmit.Model.Algo
import Minimmit.Model.Constraint
import Minimmit.Analysis.Consistency
import Minimmit.Analysis.Liveness
import Minimmit.Analysis.Responsiveness

/-!
# Minimmit の形式化

論文 arXiv:2508.10862 に基づく。`Model/` が定義、`Analysis/` が §5 の補題と定理。
import は `Transition`（遷移系）、`Certificate`（§4 の述語）、`Algo`（Algorithm 1）、
`Constraint`（制約）、`Consistency`・`Liveness`・`Responsiveness` の順で、後のファイルが
前のファイルを import する。
-/
