import Minimmit.Model.Constraint

/-!
# Consistency（§5.1）

Lemma 5.1〜5.4。部分同期は仮定しない。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-- Lemma 5.1（One vote per view）: 正直者は各 view で高々 1 つのブロックに投票する。 -/
theorem one_vote_per_view (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    {b b' : Block Tx} (hb : Sends instrs i (.vote i b)) (hb' : Sends instrs i (.vote i b'))
    (hview : b.view = b'.view) : b = b' := by
  sorry

/-- Lemma 5.2（§3 の (X1)）: b が L-notarisation を受けるなら、同じ view の他のブロックは
    M-notarisation を受けない。 -/
theorem x1 (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {b b' : Block Tx} (hL : ReceivesL f instrs b) (hview : b'.view = b.view)
    (hM : ReceivesM f instrs b') : b' = b := by
  sorry

/-- Lemma 5.3（§3 の (X2)）: b が L-notarisation を受けるなら、b の view は nullification を
    受けない。 -/
theorem x2 (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {b : Block Tx} (hL : ReceivesL f instrs b) : ¬ ReceivesNullification f instrs b.view := by
  sorry

/-- Lemma 5.4（Consistency）の本体: L-notarisation を受けた 2 つのブロックは、一方が他方の
    祖先。 -/
theorem finalised_compatible (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {b b' : Block Tx} (hL : ReceivesL f instrs b) (hL' : ReceivesL f instrs b') :
    b.Ancestor b' ∨ b'.Ancestor b := by
  sorry

/-- Consistency（§2）をブロックの形で: 正直者が L-notarisation を持つ 2 つのブロックは、
    一方が他方の祖先。log は形式化していない。論文の log_i(t) は、時刻 t に p_i の S が
    L-notarisation を持つブロックの Tr* に当たる。 -/
theorem consistency (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {i j : Fin n} (hi : Correct s₀ instrs i) (hj : Correct s₀ instrs j)
    {t t' : Nat} {b b' : Block Tx}
    (hbi : LNotarised f ((State.run s₀ instrs t).procs i).S b)
    (hbj : LNotarised f ((State.run s₀ instrs t').procs j).S b') :
    b.Ancestor b' ∨ b'.Ancestor b := by
  sorry

end Minimmit
