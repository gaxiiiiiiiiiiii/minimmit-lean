import Minimmit.Model.Certificate.Mono
import Minimmit.Model.Constraint.Basic

/-!
# §5.3 の optimistic responsiveness

論文の §5.3 の latency と optimistically responsive の定義。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

/-- 取引 tr を正直者が初めて受け取るのが t（§5.3）: t にある正直者の S にあり、t より前には
    どの正直者の S にもない。 -/
def FirstReceived (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (tr : Tx) (t : Nat) : Prop :=
  (∃ i, Correct s₀ instrs i ∧ Msg.tx tr ∈ ((State.stateAt s₀ instrs t).procs i).S)
  ∧ ∀ j t', Correct s₀ instrs j → t' < t → Msg.tx tr ∉ ((State.stateAt s₀ instrs t').procs j).S

/-- 全正直者が T までに tr を finalise している（§5.3）: T の S で finalise したブロックの Tr* に
    tr が入っている。 -/
def FinalisedByAll (f : Nat) (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (tr : Tx) (T : Nat) :
    Prop :=
  ∀ j, Correct s₀ instrs j → ∃ b : Block n Tx,
    Finalised f ((State.stateAt s₀ instrs T).procs j).S b ∧ tr ∈ b.trStar

/-- tr の latency が ℓ（§5.3）: 正直者が初めて受け取るのが t で、全正直者が初めて finalise
    しているのが t + ℓ。 -/
def Latency (f : Nat) (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (tr : Tx) (ℓ : Nat) : Prop :=
  ∃ t, FirstReceived s₀ instrs tr t ∧ FinalisedByAll f s₀ instrs tr (t + ℓ)
    ∧ ∀ ℓ' < ℓ, ¬ FinalisedByAll f s₀ instrs tr (t + ℓ')

/-- optimistically responsive（§5.3）: ある定数 c について、GST 以後に正直者が初めて受け取った
    取引の latency は c(f_a Δ + δ) 以下。δ ≤ Δ は GST 以後の遅延の上界、f_a はどの f_a + 1 個の
    連続する view にも正直なリーダーがいる数。c は n・f・Δ・δ・f_a・実行のどれにもよらない。 -/
def OptimisticallyResponsive : Prop :=
  ∃ c : Nat, ∀ {n : Nat} {Tx : Type} [DecidableEq Tx] {f Δ δ fa : Nat} {GST : Time}
    {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx},
    IsMinimmit f Δ lead GST s₀ instrs → δ ≤ Δ → PartialSync δ GST s₀ instrs →
    CorrectLeaderWithin s₀ instrs lead fa →
    ∀ (t : Nat) (tr : Tx), FirstReceived s₀ instrs tr t → GST.val ≤ t →
      ∃ ℓ ≤ c * (fa * Δ + δ), Latency f s₀ instrs tr ℓ

end Minimmit
