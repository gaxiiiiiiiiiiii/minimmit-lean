import Minimmit.Analysis.Timing

/-!
# Liveness（§5.2）

Lemma 5.5〜5.7。部分同期を仮定する。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-- 「最初の正直者が view v に入るのはスロット t」: スロット t を終えて view が v 以上に
    なった正直者がいて、それより前のスロットではいない。v = 1 なら t = 0。 -/
structure FirstEntry (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (v : View) (t : Nat) :
    Prop where
  entered : ∃ i, Correct s₀ instrs i ∧ v.val ≤ (viewAt s₀ instrs i (t + 1)).val
  first : ∀ i t', Correct s₀ instrs i → v.val ≤ (viewAt s₀ instrs i (t' + 1)).val → t ≤ t'

/-- Lemma 5.5（Progression through views）: 正直者はすべての view に入る。 -/
theorem progression (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hs : PartialSync Δ s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i) (v : View) :
    ∃ t, v.val ≤ (viewAt s₀ instrs i t).val := by
  sorry

/-- Lemma 5.6（Correct leaders finalise blocks）: lead(v) が正直で、最初の正直者が GST 以降に
    view v に入るなら、lead(v) はブロックを送り、それは L-notarisation を受ける。 -/
theorem correct_leader_finalises (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hs : PartialSync Δ s₀ instrs) {v : View} (hi : Correct s₀ instrs (lead v))
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : hs.GST.val ≤ t) :
    ∃ b : Block Tx, b.view = v ∧ Sends instrs (lead v) (.block (lead v) b)
      ∧ ReceivesL f instrs b := by
  sorry

/-- Lemma 5.7（Liveness）: 正直者 p_i が受け取った取引は、正直者 p_j が L-notarisation を
    持つブロックの Tr* にいつか入る。 -/
theorem liveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hs : PartialSync Δ s₀ instrs) (hlead : Fair lead)
    {i j : Fin n} (hi : Correct s₀ instrs i) (hj : Correct s₀ instrs j)
    {t : Nat} {tr : Tx} (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S) :
    ∃ t' b, LNotarised f ((State.run s₀ instrs t').procs j).S b ∧ tr ∈ b.trStar := by
  sorry

end Minimmit
