import Minimmit.Analysis.Consistency.Lemma5_2
import Mathlib.Data.Finset.Max

/-!
# Lemma 5.3（(X2)）
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-- Lemma 5.3（§3 の (X2)）: b が L-notarisation を受けるなら、b の view は nullification を
    受けない。 -/
theorem not_receivesNullification_of_receivesL (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {b : Block n Tx} (hL : ReceivesL f instrs b) : ¬ ReceivesNullification f instrs b.view := by
  intro hN
  classical
  rcases hL with rfl | hL
  · -- genesis: view 0 の nullify を正直者は送らない
    have hlt : f < (nullifySenders instrs Block.gen.view).card := lt_of_lt_of_le (by omega) hN
    obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb hlt
    obtain ⟨t, j, ht⟩ := mem_nullifySenders.mp hq
    have h1 := ((localInv_run hinit hh hqc (t + 1)).null_view _ (mem_S_succ_of_send hh hqc ht)).1
    simp [Block.view] at h1
  set P := voteSenders instrs b with hP
  set N := nullifySenders instrs b.view with hNdef
  have hN' : 2 * f + 1 ≤ N.card := hN
  have hinter := card_inter_add_n_ge P N
  -- C: P ∩ N の正直者。空でない
  set C := (P ∩ N).filter (fun q => Correct s₀ instrs q) with hC
  have hCne : C.Nonempty := by
    have hlt : f < (P ∩ N).card := by omega
    obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb hlt
    exact ⟨q, Finset.mem_filter.mpr ⟨hq, hqc⟩⟩
  -- T q: q が最初に nullify(b.view) を送るスロット
  have hT : ∃ T : Fin n → Nat,
      (∀ q, (∃ t, ∃ j, Action.send (Msg.nullify q b.view) j ∈ (instrs t).actions q) →
        ∃ j, Action.send (Msg.nullify q b.view) j ∈ (instrs (T q)).actions q)
      ∧ (∀ q, (∃ t, ∃ j, Action.send (Msg.nullify q b.view) j ∈ (instrs t).actions q) →
        ∀ t, (∃ j, Action.send (Msg.nullify q b.view) j ∈ (instrs t).actions q) → T q ≤ t) := by
    refine ⟨fun q => if hq : ∃ t, ∃ j, Action.send (Msg.nullify q b.view) j ∈ (instrs t).actions q
      then Nat.find hq else 0, fun q hq => ?_, fun q hq t ht => ?_⟩
    · simp only [dif_pos hq]; exact Nat.find_spec hq
    · simp only [dif_pos hq]; exact Nat.find_min' hq ht
  obtain ⟨T, hT_spec, hT_min⟩ := hT
  obtain ⟨q₀, hq₀C, hmin⟩ := Finset.exists_min_image C T hCne
  obtain ⟨hq₀PN, hq₀c⟩ := Finset.mem_filter.mp hq₀C
  obtain ⟨hq₀P, hq₀N⟩ := Finset.mem_inter.mp hq₀PN
  have hexq₀ : ∃ t, ∃ j, Action.send (Msg.nullify q₀ b.view) j ∈ (instrs t).actions q₀ :=
    mem_nullifySenders.mp hq₀N
  obtain ⟨j₀, hj₀⟩ := hT_spec q₀ hexq₀
  have hj₀' := hj₀
  have hact := hh (T q₀) q₀ (hq₀c (T q₀))
  rw [hact] at hj₀
  have hp : Algo.LocalInv f q₀ ((State.run s₀ instrs (T q₀)).procs q₀) :=
    localInv_run hinit hh hq₀c (T q₀)
  -- 最初の nullify なので、その前の S に自分の nullify は無い
  have hno : Msg.nullify q₀ b.view ∉ ((State.run s₀ instrs (T q₀)).procs q₀).S := by
    intro hmem
    obtain ⟨t', ht', j', hj'⟩ := sendsBefore_of_mem_S hinit hmem rfl
    have := hT_min q₀ hexq₀ t' ⟨j', hj'⟩
    omega
  -- b への票: 最初に送るスロット t₁
  have hexv : ∃ t, ∃ j, Action.send (Msg.vote q₀ b) j ∈ (instrs t).actions q₀ :=
    mem_voteSenders.mp hq₀P
  obtain ⟨j₁, hj₁⟩ := Nat.find_spec hexv
  have hvote_no : Msg.vote q₀ b ∉ ((State.run s₀ instrs (Nat.find hexv)).procs q₀).S := by
    intro hmem
    obtain ⟨t', ht', j', hj'⟩ := sendsBefore_of_mem_S hinit hmem rfl
    exact absurd (Nat.find_min' hexv ⟨j', hj'⟩) (not_le.mpr ht')
  have hbvote : Msg.vote q₀ b ∈ ((State.run s₀ instrs (T q₀)).procs q₀).S
      ∨ Action.send (Msg.vote q₀ b) j₁
      ∈ Algo.step f Δ lead q₀ ((State.run s₀ instrs (T q₀)).procs q₀) := by
    rcases lt_trichotomy (Nat.find hexv) (T q₀) with hlt | heq | hgt
    · left
      exact S_subset_run s₀ instrs q₀ (Nat.succ_le_of_lt hlt) (mem_S_succ_of_send hh hq₀c hj₁)
    · right
      have hact₁ := hh (Nat.find hexv) q₀ (hq₀c _)
      rw [hact₁] at hj₁
      rw [heq] at hj₁
      exact hj₁
    · exfalso
      -- t₀ に nullify(b.view) を出した後、view b.view で b に投票できない
      have hnull_mem : Msg.nullify q₀ b.view ∈ ((State.run s₀ instrs (Nat.find hexv)).procs q₀).S :=
        S_subset_run s₀ instrs q₀ (Nat.succ_le_of_lt hgt) (mem_S_succ_of_send hh hq₀c hj₀')
      have hact₁ := hh (Nat.find hexv) q₀ (hq₀c _)
      rw [hact₁] at hj₁
      rcases Algo.vote_emission (localInv_run hinit hh hq₀c _) hj₁
          with hmem | ⟨q, hq, hqv, _, hqnl, hqS, _, _⟩
      · exact hvote_no hmem
      · have := hq.null_flag (by rw [hqv]; exact hqS hnull_mem)
        rw [hqnl] at this
        cases this
  obtain ⟨h6, hv6, hnl6, hvote6, hnp⟩ := Algo.nullify_after_vote hp hbvote hj₀ hno
  -- 証拠の署名者 W を数える
  set W := noProgressWitnesses (Algo.st4 f Δ lead q₀ ((State.run s₀ instrs (T q₀)).procs q₀)).S
    b.view (some b) with hW
  have hWcard : 2 * f + 1 ≤ W.card := hnp
  have hWsub : W ⊆ Pᶜ ∪ W.filter (fun w => ¬ Correct s₀ instrs w) := by
    intro w hw
    rw [Finset.mem_union]
    by_cases hwP : w ∈ P
    · by_cases hwc : Correct s₀ instrs w
      · exfalso
        have hwit := mem_noProgressWitnesses.mp hw
        cases hwit with
        | nullify hm =>
          by_cases hwq : w = q₀
          · subst hwq
            have := h6.null_flag (by rw [hv6]; exact hm)
            rw [hnl6] at this
            cases this
          · rcases Algo.mem_S_stage_or f Δ lead q₀ _ (Algo.S_st4_subset_st5 f Δ lead q₀ _ hm)
              with hm' | hs
            · obtain ⟨t', ht', j', hj'⟩ := sendsBefore_of_mem_S hinit hm' rfl
              have hwC : w ∈ C := Finset.mem_filter.mpr
                ⟨Finset.mem_inter.mpr ⟨hwP, mem_nullifySenders.mpr ⟨t', j', hj'⟩⟩, hwc⟩
              have h1 := hmin w hwC
              have h2 := hT_min w ⟨t', j', hj'⟩ t' ⟨j', hj'⟩
              omega
            · simp only [Msg.signer, Option.some.injEq] at hs
              exact hwq hs
        | vote b'' hbv hne hm =>
          by_cases hwq : w = q₀
          · subst hwq
            exact hne (congrArg some (h6.unique b'' b hm hvote6 hbv))
          · rcases Algo.mem_S_stage_or f Δ lead q₀ _ (Algo.S_st4_subset_st5 f Δ lead q₀ _ hm)
              with hm' | hs
            · have hs'' := sends_of_mem_S hinit hm' rfl
              have := one_vote_per_view hinit hh hwc (mem_voteSenders.mp hwP) hs'' hbv.symm
              exact hne (congrArg some this.symm)
            · simp only [Msg.signer, Option.some.injEq] at hs
              exact hwq hs
      · exact Or.inr (Finset.mem_filter.mpr ⟨hw, hwc⟩)
    · exact Or.inl (Finset.mem_compl.mpr hwP)
  have hcard := Finset.card_le_card hWsub
  have h1 := Finset.card_union_le Pᶜ (W.filter (fun w => ¬ Correct s₀ instrs w))
  have h2 : Pᶜ.card = n - P.card := by rw [Finset.card_compl, Fintype.card_fin]
  have h3 : (W.filter (fun w => ¬ Correct s₀ instrs w)).card ≤ f :=
    card_le_of_byz hb _ fun w hw => exists_byz_of_not_correct (Finset.mem_filter.mp hw).2
  omega

end Minimmit
