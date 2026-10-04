import Minimmit.Analysis.Consistency.Lemma5_1

/-!
# Lemma 5.2（(X1)）
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ : Nat} {GST : Time} {lead : View → Fin n}
variable {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-- Lemma 5.2（§3 の (X1)）: b が L-notarisation を受けるなら、同じ view の他のブロックは
    M-notarisation を受けない。 -/
theorem receivesM_unique_of_receivesL (hprot : IsMinimmit f Δ lead GST s₀ instrs)
    {b b' : Block n Tx} (hL : ReceivesL f s₀ instrs b) (hview : b'.view = b.view)
    (hM : ReceivesM f s₀ instrs b') : b' = b := by
  have ⟨hn, hinit, hh, hb, _, _⟩ := hprot
  rcases hM with rfl | hM
  · rcases hL with rfl | hL
    · rfl
    · by_cases hg : b = .gen
      · exact hg.symm
      exfalso
      have hlt : f < (voteSenders s₀ instrs b).card := lt_of_lt_of_le (by omega) hL
      obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb hlt
      have h1 := one_le_view_of_sends hinit hh hqc (mem_voteSenders.mp hq) hg
      rw [← hview] at h1
      simp [Block.view] at h1
  · rcases hL with rfl | hL
    · by_cases hg : b' = .gen
      · exact hg
      exfalso
      have hlt : f < (voteSenders s₀ instrs b').card := lt_of_lt_of_le (by omega) hM
      obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb hlt
      have h1 := one_le_view_of_sends hinit hh hqc (mem_voteSenders.mp hq) hg
      rw [hview] at h1
      simp [Block.view] at h1
    · have hinter := card_inter_add_n_ge (voteSenders s₀ instrs b) (voteSenders s₀ instrs b')
      have hlt : f < (voteSenders s₀ instrs b ∩ voteSenders s₀ instrs b').card := by omega
      obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb hlt
      rw [Finset.mem_inter] at hq
      exact (one_vote_per_view hprot hqc (mem_voteSenders.mp hq.1) (mem_voteSenders.mp hq.2)
        hview.symm).symm

end Minimmit
