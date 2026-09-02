import Minimmit.Analysis.Run
import Mathlib.Data.Finset.Max

/-!
# Consistency（§5.1）

Lemma 5.1〜5.4。部分同期は仮定しない。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-! ### 正直者の局所不変量を実行に沿って保つ -/

/-- S は時間とともに減らない。 -/
theorem S_subset_run (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (i : Fin n) {t t' : Nat}
    (h : t ≤ t') : ((State.run s₀ instrs t).procs i).S ⊆ ((State.run s₀ instrs t').procs i).S := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (State.S_subset_step _ _ i)

/-- 正直者 p_i がスロット t に送った message は、スロット t + 1 の S にある。 -/
theorem mem_S_succ_of_send (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    {t : Nat} {m : Msg n Tx} {j : Fin n} (h : Action.send m j ∈ (instrs t).actions i) :
    m ∈ ((State.run s₀ instrs (t + 1)).procs i).S := by
  have hact := hh t i (hi t)
  rw [hact] at h
  have hm := Algo.mem_S_of_send_step h
  rw [← Algo.executeAll_step, ← hact] at hm
  have hsub := (State.step_procs (State.run s₀ instrs t) (instrs t) i).S
  rw [Processor.tick_S] at hsub
  exact hsub hm

/-- 正直者 p_i の署名付きの message がスロット t + 1 の S にあれば、スロット t の動作の後の
    S に既にある。配送で初めて入ることはない。 -/
theorem own_mem_act_of_mem_succ (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {m : Msg n Tx} (hm : m.signer = some i)
    (h : m ∈ ((State.run s₀ instrs (t + 1)).procs i).S) :
    m ∈ (((State.run s₀ instrs t).act (instrs t)).procs i).S := by
  obtain ⟨t', ht', j, hj⟩ := sendsBefore_of_mem_S hinit h hm
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
  · have hmem := mem_S_succ_of_send hh hi hj
    have hsub := S_subset_run s₀ instrs i (Nat.succ_le_of_lt ht')
    rw [State.act_procs]
    exact Processor.S_subset_executeAll i _ _ (hsub hmem)
  · have hact := hh t' i (hi t')
    rw [State.act_procs, hact, Algo.executeAll_step]
    rw [hact] at hj
    exact Algo.mem_S_of_send_step hj

omit [DecidableEq Tx] in
theorem localInv_init (hinit : Init s₀) (i : Fin n) : Algo.LocalInv f i (s₀.procs i) := by
  rw [hinit.procs i]
  refine ⟨⟨le_refl 1, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [Processor.init]

theorem localInv_step (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) (t : Nat) (h : Algo.LocalInv f i ((State.run s₀ instrs t).procs i)) :
    Algo.LocalInv f i ((State.run s₀ instrs (t + 1)).procs i) := by
  have hact := hh t i (hi t)
  have hloc : Algo.LocalInv f i ((((State.run s₀ instrs t).procs i).executeAll i
      ((instrs t).actions i)).tick ((State.run s₀ instrs t).procs i).S) := by
    rw [hact, Algo.executeAll_step]
    exact (h.stepPair Δ lead).tick _
  refine hloc.of_sgrows (State.step_procs _ _ i) (fun c hc => ?_) (fun w hw => ?_)
  · rw [Processor.tick_S, ← State.act_procs]; exact own_mem_act_of_mem_succ hinit hh hi rfl hc
  · rw [Processor.tick_S, ← State.act_procs]; exact own_mem_act_of_mem_succ hinit hh hi rfl hw

/-- 正直者 p_i の局所不変量は全スロットで成り立つ。 -/
theorem localInv_run (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) : ∀ t, Algo.LocalInv f i ((State.run s₀ instrs t).procs i)
  | 0 => localInv_init hinit i
  | t + 1 => localInv_step hinit hh hi t (localInv_run hinit hh hi t)

omit [DecidableEq Tx] in
theorem mem_voteSenders {q : Fin n} {b : Block Tx} :
    q ∈ voteSenders instrs b ↔ Sends instrs q (Msg.vote q b) := by
  simp [voteSenders]

omit [DecidableEq Tx] in
theorem mem_nullifySenders {q : Fin n} {v : View} :
    q ∈ nullifySenders instrs v ↔ Sends instrs q (Msg.nullify q v) := by
  simp [nullifySenders]

/-! ### Lemma 5.1〜5.4 -/

/-- Lemma 5.1（One vote per view）: 正直者は各 view で高々 1 つのブロックに投票する。 -/
theorem one_vote_per_view (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    {b b' : Block Tx} (hb : Sends instrs i (.vote i b)) (hb' : Sends instrs i (.vote i b'))
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
    (hi : Correct s₀ instrs i) {b : Block Tx} (hb : Sends instrs i (Msg.vote i b)) :
    1 ≤ b.view.val := by
  obtain ⟨t, j, ht⟩ := hb
  exact ((localInv_run hinit hh hi (t + 1)).notar b (mem_S_succ_of_send hh hi ht)).1

/-- Lemma 5.2（§3 の (X1)）: b が L-notarisation を受けるなら、同じ view の他のブロックは
    M-notarisation を受けない。 -/
theorem x1 (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {b b' : Block Tx} (hL : ReceivesL f instrs b) (hview : b'.view = b.view)
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

/-- Lemma 5.3（§3 の (X2)）: b が L-notarisation を受けるなら、b の view は nullification を
    受けない。 -/
theorem x2 (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {b : Block Tx} (hL : ReceivesL f instrs b) : ¬ ReceivesNullification f instrs b.view := by
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
      ∨ Action.send (Msg.vote q₀ b) j₁ ∈ Algo.step f Δ lead q₀ ((State.run s₀ instrs (T q₀)).procs q₀) := by
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
      rcases Algo.vote_emission (localInv_run hinit hh hq₀c _) hj₁ with hmem | ⟨q, hq, hqv, _, hqnl, hqS, _, _⟩
      · exact hvote_no hmem
      · have := hq.null_flag (by rw [hqv]; exact hqS hnull_mem)
        rw [hqnl] at this
        cases this
  obtain ⟨h6, hv6, hnl6, hvote6, hnp⟩ := Algo.nullify_after_vote hp hbvote hj₀ hno
  -- 証拠の署名者 W を数える
  set W := noProgressWitnesses (Algo.st6 f Δ lead q₀ ((State.run s₀ instrs (T q₀)).procs q₀)).S
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
          · rcases Algo.mem_S_stage_or f Δ lead q₀ _ hm with hm' | hs
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
          · rcases Algo.mem_S_stage_or f Δ lead q₀ _ hm with hm' | hs
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

omit [DecidableEq Tx] in
theorem receivesM_of_receivesL (hn : 5 * f + 1 ≤ n) {b : Block Tx} (hL : ReceivesL f instrs b) :
    ReceivesM f instrs b :=
  hL.imp_right fun h => le_trans (by omega) h

theorem one_le_view_of_receivesL (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs) {b : Block Tx}
    (hL : ReceivesL f instrs b) (hg : b ≠ .gen) : 1 ≤ b.view.val := by
  rcases hL with rfl | hL
  · exact absurd rfl hg
  · obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb (lt_of_lt_of_le (by omega) hL)
    exact one_le_view_of_sends hinit hh hqc (mem_voteSenders.mp hq)

/-- M-notarisation を受けた genesis でないブロックには、9〜11 行で投票した正直者がいる。
    その段の入力 st2 の S に valid proposal がある。 -/
theorem exists_valid_proposal_vote (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) {b₂ : Block Tx} (hg : b₂ ≠ .gen) (hM : ReceivesM f instrs b₂) :
    ∃ q t, Correct s₀ instrs q
      ∧ (Algo.st2 f lead q ((State.run s₀ instrs t).procs q)).view = b₂.view
      ∧ ValidProposal f lead (Algo.st2 f lead q ((State.run s₀ instrs t).procs q)).S
          (Algo.st2 f lead q ((State.run s₀ instrs t).procs q)).view b₂ := by
  classical
  have hex : ∃ t, ∃ q, Correct s₀ instrs q ∧ ∃ j, Action.send (Msg.vote q b₂) j ∈ (instrs t).actions q := by
    rcases hM with rfl | hM
    · exact absurd rfl hg
    · obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb (lt_of_lt_of_le (by omega) hM)
      obtain ⟨t, j, h⟩ := mem_voteSenders.mp hq
      exact ⟨t, q, hqc, j, h⟩
  obtain ⟨q, hqc, j, hj⟩ := Nat.find_spec hex
  have hmin : ∀ t' < Nat.find hex, ∀ w, Correct s₀ instrs w → ∀ j',
      Action.send (Msg.vote w b₂) j' ∈ (instrs t').actions w → False :=
    fun t' ht' w hw j' h => absurd (Nat.find_min' hex ⟨w, hw, j', h⟩) (not_le.mpr ht')
  have hact := hh (Nat.find hex) q (hqc _)
  rw [hact] at hj
  rw [Algo.step_eq_stepPair, Algo.stepPair_snd] at hj
  simp only [List.mem_append] at hj
  rcases hj with ((((((hj | hj) | hj) | hj) | hj) | hj) | hj)
  · obtain ⟨t', ht', j', hj'⟩ := sendsBefore_of_mem_S hinit (Algo.send_forwardNew_mem hj) rfl
    exact absurd hj' (hmin t' ht' q hqc j')
  · obtain ⟨_, hm⟩ := Algo.send_propose_eq hj; cases hm
  · obtain ⟨b', hm, hbv, _, _, hvp, _⟩ := Algo.send_voteProposal_eq hj
    injection hm with _ hbb
    subst hbb
    exact ⟨q, Nat.find hex, hqc, hbv.symm, hvp⟩
  · obtain ⟨hm, _⟩ := Algo.send_nullifyTimeout_eq hj; cases hm
  · exact absurd hj Algo.send_advanceNull
  · obtain ⟨b', hm, _, hM5, _, _, _⟩ := Algo.send_advanceM_eq hj
    injection hm with _ hbb
    subst hbb
    rcases hM5 with hg' | hM5
    · exact absurd hg' hg
    obtain ⟨w, hw, hwc⟩ := exists_correct_of_lt_card hb (lt_of_lt_of_le (by omega) hM5)
    have hwm := mem_voters.mp hw
    rcases Algo.mem_S_st5 hwm with hwm | ⟨v, hv⟩
    · rcases Algo.mem_S_st3 hwm with hwm | ⟨b'', hb'', hsend⟩
      · rcases Algo.mem_S_st2 hwm with hwm | ⟨b'', hb''⟩
        · obtain ⟨t', ht', j', hj'⟩ := sendsBefore_of_mem_S hinit hwm rfl
          exact absurd hj' (hmin t' ht' w hwc j')
        · cases hb''
      · injection hb'' with hwq hbb
        subst hwq
        subst hbb
        obtain ⟨b', hm, hbv, _, _, hvp, _⟩ := Algo.send_voteProposal_eq hsend
        injection hm with _ hbb
        subst hbb
        exact ⟨w, Nat.find hex, hwc, hbv.symm, hvp⟩
    · cases hv
  · obtain ⟨hm, _⟩ := Algo.send_nullifyNoProgress_eq hj; cases hm

/-- 正直者の st2 の S にある M-notarisation は、実行上の M-notarisation。 -/
theorem receivesM_of_MNotarised_st2 (hinit : Init s₀) {q : Fin n} {t : Nat} {b₀ : Block Tx}
    (h : MNotarised f (Algo.st2 f lead q ((State.run s₀ instrs t).procs q)).S b₀) :
    ReceivesM f instrs b₀ := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    refine h.trans (Finset.card_le_card fun w hw => ?_)
    rw [mem_voters] at hw
    rw [mem_voteSenders]
    rcases Algo.mem_S_st2 hw with hw | ⟨b, hb⟩
    · exact sends_of_mem_S hinit hw rfl
    · cases hb

theorem receivesNullification_of_Nullified_st2 (hinit : Init s₀) {q : Fin n} {t : Nat} {w : View}
    (h : Nullified f (Algo.st2 f lead q ((State.run s₀ instrs t).procs q)).S w) :
    ReceivesNullification f instrs w := by
  refine h.trans (Finset.card_le_card fun x hx => ?_)
  rw [mem_nullifiers] at hx
  rw [mem_nullifySenders]
  rcases Algo.mem_S_st2 hx with hx | ⟨b, hb⟩
  · exact sends_of_mem_S hinit hx rfl
  · cases hb

/-- M-notarisation を受けたブロックの親は M-notarisation を受け、親の view と自分の view の
    間の view は nullification を受ける。 -/
theorem receivesM_parent (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) {v : View} {tr : List Tx} {p₀ : Block Tx}
    (hM : ReceivesM f instrs (Block.node v tr p₀)) :
    ReceivesM f instrs p₀
      ∧ ∀ w : View, p₀.view.val < w.val → w.val < v.val → ReceivesNullification f instrs w := by
  obtain ⟨q, t, _, hview, hvp⟩ := exists_valid_proposal_vote hinit hh hb (by simp) hM
  have hpar : p₀ ∈ (Block.node v tr p₀).parent := by simp [Block.parent]
  refine ⟨receivesM_of_MNotarised_st2 hinit (hvp.parent p₀ hpar), fun w h1 h2 => ?_⟩
  refine receivesNullification_of_Nullified_st2 hinit (hvp.gaps p₀ hpar w h1 ?_)
  rw [hview]; exact h2

/-- M-notarisation を受けたブロックの祖先は M-notarisation を受ける。 -/
theorem receivesM_ancestor (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) {c b : Block Tx} (hanc : Block.Ancestor c b)
    (hM : ReceivesM f instrs b) : ReceivesM f instrs c := by
  induction hanc with
  | refl => exact hM
  | parent v tr p _ ih => exact ih (receivesM_parent hinit hh hb hM).1

/-- Lemma 5.4（Consistency）の本体: L-notarisation を受けた 2 つのブロックは、一方が他方の
    祖先。 -/
theorem finalised_compatible (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {b b' : Block Tx} (hL : ReceivesL f instrs b) (hL' : ReceivesL f instrs b') :
    b.Ancestor b' ∨ b'.Ancestor b := by
  by_contra hcon
  simp only [not_or] at hcon
  wlog hle : b.view.val ≤ b'.view.val generalizing b b' with H
  · exact H hL' hL ⟨hcon.2, hcon.1⟩ (not_le.mp hle).le
  have hbg : b ≠ .gen := fun h => hcon.1 (h ▸ Block.gen_ancestor b')
  have hv₁ := one_le_view_of_receivesL hn hinit hh hb hL hbg
  obtain ⟨v, tr, p₀, hanc, hge, hlt⟩ := Block.exists_crossing hv₁ hle
  have hM : ReceivesM f instrs (Block.node v tr p₀) :=
    receivesM_ancestor hinit hh hb hanc (receivesM_of_receivesL hn hL')
  have hna : ¬ b.Ancestor (Block.node v tr p₀) := fun h => hcon.1 (h.trans hanc)
  have hne : v.val ≠ b.view.val := by
    intro heq
    have hv : (Block.node v tr p₀).view = b.view := View.val_injective heq
    have := x1 hn hinit hh hb hL hv hM
    exact hna (this ▸ Block.Ancestor.refl _)
  obtain ⟨_, hgap⟩ := receivesM_parent hinit hh hb hM
  exact x2 hn hinit hh hb hL (hgap b.view hlt (lt_of_le_of_ne hge (Ne.symm hne)))

/-- 正直者の S にある L-notarisation は、実行上の L-notarisation。 -/
theorem receivesL_of_LNotarised (hinit : Init s₀) {i : Fin n} {t : Nat} {b : Block Tx}
    (h : LNotarised f ((State.run s₀ instrs t).procs i).S b) : ReceivesL f instrs b := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    refine h.trans (Finset.card_le_card fun w hw => ?_)
    rw [mem_voters] at hw
    rw [mem_voteSenders]
    exact sends_of_mem_S hinit hw rfl

/-- Consistency（§2）をブロックの形で: 正直者が L-notarisation を持つ 2 つのブロックは、
    一方が他方の祖先。log は形式化していない。論文の log_i(t) は、時刻 t に p_i の S が
    L-notarisation を持つブロックの Tr* に当たる。 -/
theorem consistency (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {i j : Fin n} (_hi : Correct s₀ instrs i) (_hj : Correct s₀ instrs j)
    {t t' : Nat} {b b' : Block Tx}
    (hbi : LNotarised f ((State.run s₀ instrs t).procs i).S b)
    (hbj : LNotarised f ((State.run s₀ instrs t').procs j).S b') :
    b.Ancestor b' ∨ b'.Ancestor b :=
  finalised_compatible hn hinit hh hb (receivesL_of_LNotarised hinit hbi)
    (receivesL_of_LNotarised hinit hbj)

end Minimmit
