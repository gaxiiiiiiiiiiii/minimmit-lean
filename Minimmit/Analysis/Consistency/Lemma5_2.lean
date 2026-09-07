import Minimmit.Analysis.Consistency.Lemma5_1

/-!
# Lemma 5.2（(X1)）
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-- Lemma 5.2（§3 の (X1)）: b が L-notarisation を受けるなら、同じ view の他のブロックは
    M-notarisation を受けない。 -/
theorem receivesM_unique_of_receivesL (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {b b' : Block n Tx} (hL : ReceivesL f instrs b) (hview : b'.view = b.view)
    (hM : ReceivesM f instrs b') : b' = b := by
  rcases hM with rfl | hM
  · rcases hL with rfl | hL
    · rfl
    · exfalso
      have hlt : f < (voteSenders instrs b).card := lt_of_lt_of_le (by omega) hL
      obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb hlt
      have h1 := one_le_view_of_sends hinit hh hqc (mem_voteSenders.mp hq)
      rw [← hview] at h1
      simp [Block.view] at h1
  · rcases hL with rfl | hL
    · exfalso
      have hlt : f < (voteSenders instrs b').card := lt_of_lt_of_le (by omega) hM
      obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb hlt
      have h1 := one_le_view_of_sends hinit hh hqc (mem_voteSenders.mp hq)
      rw [hview] at h1
      simp [Block.view] at h1
    · have hinter := card_inter_add_n_ge (voteSenders instrs b) (voteSenders instrs b')
      have hlt : f < (voteSenders instrs b ∩ voteSenders instrs b').card := by omega
      obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb hlt
      rw [Finset.mem_inter] at hq
      exact (one_vote_per_view hinit hh hqc (mem_voteSenders.mp hq.1) (mem_voteSenders.mp hq.2)
        hview.symm).symm

end Minimmit
