import Minimmit.Model.Constraint.Run

/-!
# Lemma 5.1（One vote per view）
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-- Lemma 5.1（One vote per view）: 正直者は各 view で高々 1 つのブロックに投票する。 -/
theorem one_vote_per_view (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    {b b' : Block n Tx} (hb : Sends instrs i (.vote i b)) (hb' : Sends instrs i (.vote i b'))
    (hview : b.view = b'.view) : b = b' := by
  obtain ⟨t, j, ht⟩ := hb
  obtain ⟨t', j', ht'⟩ := hb'
  have h₁ := mem_S_succ_of_send hh hi ht
  have h₂ := mem_S_succ_of_send hh hi ht'
  have hle₁ : t + 1 ≤ max (t + 1) (t' + 1) := le_max_left _ _
  have hle₂ : t' + 1 ≤ max (t + 1) (t' + 1) := le_max_right _ _
  exact (localInv_run hinit hh hi (max (t + 1) (t' + 1))).unique b b'
    (S_subset_run s₀ instrs i hle₁ h₁) (S_subset_run s₀ instrs i hle₂ h₂) hview

/-- 正直者が投票するブロックの view は 1 以上。 -/
theorem one_le_view_of_sends (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {b : Block n Tx} (hb : Sends instrs i (Msg.vote i b)) :
    1 ≤ b.view.val := by
  obtain ⟨t, j, ht⟩ := hb
  have hL := localInv_run hinit hh hi t
  rw [hh t i (hi t), Algo.step_eq_stepPair, Algo.stepPair_snd'] at ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨q, hLq, hqv, _⟩ := Algo.vote_emission_core hL ht
    rw [← hqv]; exact hLq.view_pos
  · -- 転送: 新しく M-notarised になったブロック。genesis は初期の S で既に M-notarised
    have hfw := Algo.send_forwardNew_mem_forwardMsgs ht
    obtain ⟨h1, h2⟩ := Algo.of_mem_forwardMsgs_vote hfw
    have hg : b ≠ .gen := by
      rintro rfl
      rw [Algo.st5_prevS] at h2
      exact h2 (MNotarised.gen_of h1 (genesisS_subset_prevS_run hinit i t))
    rcases Algo.mem_S_stage_or_sent f Δ lead i _ (Algo.mem_S_of_mem_forwardMsgs hfw)
      with hm | ⟨_, j', hs⟩
    · exact (hL.notar b hg hm).1
    · obtain ⟨q, hLq, hqv, _⟩ := Algo.vote_emission_core hL hs
      rw [← hqv]; exact hLq.view_pos

end Minimmit
