import Minimmit.Model.Certificate.Mono
import Minimmit.Model.Constraint.Basic

/-!
# §5.3 の optimistic responsiveness

論文の §5.3 の定義を、そのまま述語にする。プロトコルがこれを満たすことは
`optimistic_responsiveness`。
-/

namespace Minimmit

/-- optimistically responsive（§5.3）: ある定数 c について、GST 以後の時刻 t に正直者が初めて
    受け取った取引は、t + c(f_a Δ + δ) までに全正直者が finalise する。δ ≤ Δ は GST 以後の遅延の
    上界、f_a はどの f_a + 1 個の連続する view にも正直なリーダーがいる数。c は n・f・Δ・δ・f_a・
    実行のどれにもよらない。 -/
def OptimisticallyResponsive : Prop :=
  ∃ c : Nat, ∀ {n : Nat} {Tx : Type} [DecidableEq Tx] {f Δ δ fa : Nat} {GST : Time}
    {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx},
    IsMinimmit f Δ lead GST s₀ instrs → δ ≤ Δ → PartialSync δ GST s₀ instrs →
    CorrectLeaderWithin s₀ instrs lead fa →
    ∀ i, Correct s₀ instrs i → ∀ (t : Nat) (tr : Tx),
      Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S →
      (∀ j t', Correct s₀ instrs j → t' < t → Msg.tx tr ∉ ((State.run s₀ instrs t').procs j).S) →
      GST.val ≤ t →
      ∀ j, Correct s₀ instrs j → ∃ b : Block n Tx,
        Finalised f ((State.run s₀ instrs (t + c * (fa * Δ + δ))).procs j).S b ∧ tr ∈ b.trStar

end Minimmit
