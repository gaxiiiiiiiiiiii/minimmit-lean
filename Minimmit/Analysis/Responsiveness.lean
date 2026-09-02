import Minimmit.Analysis.Liveness

/-!
# Optimistic responsiveness（§5.3）

Lemma 5.8〜5.10。δ ≤ Δ は GST 後の実際の遅延の上界、f_a ≤ f は実際に腐敗する人数。
論文の O(·) は、証明中の具体的な bound で置き換えている。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-- Lemma 5.8: lead(v) が正直で、最初の正直者が t ≥ GST に view v に入るなら、正直者は
    全員 t + 3δ までに view v のブロックを finalise し、view v を離れる。 -/
theorem correct_leader_finalises_fast (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hv : Valid s₀ instrs) (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ s₀ instrs) {v : View} (hi : Correct s₀ instrs (lead v))
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : hs.GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j →
      (∃ b : Block Tx, b.view = v ∧ LNotarised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S b)
      ∧ v.val < (viewAt s₀ instrs j (t + 3 * δ + 1)).val := by
  sorry

/-- Lemma 5.9: 最初の正直者が t ≥ GST に view v に入るなら、lead(v) が正直かどうかに
    よらず、正直者は全員 t + 2Δ + 3δ までに view v を離れる。 -/
theorem leave_view (hn : 5 * f + 1 ≤ n) (hinit : Init s₀) (hv : Valid s₀ instrs)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ s₀ instrs) {v : View}
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : hs.GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j → v.val < (viewAt s₀ instrs j (t + 2 * Δ + 3 * δ + 1)).val := by
  sorry

/-- Lemma 5.10（Optimistic responsiveness）: 取引 tr を正直者が初めて受け取るのが t ≥ GST
    なら、正直者は全員 t + δ + (f_a + 1)(2Δ + 3δ) + 3δ までに tr を finalise する。
    どの f_a + 1 個の連続する view にも正直なリーダーがいることを仮定する（論文の
    lead(v) = p_{(v mod n)+1} は f_a 人以下の腐敗のもとでこれを満たす）。 -/
theorem optimistic_responsiveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hv : Valid s₀ instrs) (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ s₀ instrs) {fa : Nat} (hfa : ByzBound fa s₀ instrs)
    (hlead : ∀ v : View, ∃ v' : View, v.val ≤ v'.val ∧ v'.val ≤ v.val + fa
      ∧ Correct s₀ instrs (lead v'))
    {i : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {tr : Tx}
    (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S)
    (hfirst : ∀ j t', Correct s₀ instrs j → t' < t → Msg.tx tr ∉ ((State.run s₀ instrs t').procs j).S)
    (hgst : hs.GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j → ∃ b : Block Tx,
      LNotarised f ((State.run s₀ instrs (t + δ + (fa + 1) * (2 * Δ + 3 * δ) + 3 * δ)).procs j).S b
      ∧ tr ∈ b.trStar := by
  sorry

end Minimmit
