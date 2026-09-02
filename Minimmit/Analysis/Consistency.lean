import Minimmit.Analysis.Run

/-!
# Consistency（§5.1）

Lemma 5.1〜5.4。部分同期は仮定しない。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-! ### 実行全体の不変量 -/

/-- p_i の署名付きの票の出所: どこかの S か pool にあれば、p_i 自身の S にある。署名が偽造
    できないことの帰結。 -/
structure Origin (i : Fin n) (s : State n Tx) : Prop where
  procs : ∀ k c, Msg.vote i c ∈ (s.procs k).S → Msg.vote i c ∈ (s.procs i).S
  pool : ∀ x ∈ s.pool, ∀ c, x.msg = Msg.vote i c → Msg.vote i c ∈ (s.procs i).S

/-- p_i についての不変量: 票の出所と、局所状態の `VoteInv`。 -/
structure Inv (i : Fin n) (s : State n Tx) : Prop where
  origin : Origin i s
  vote : Algo.VoteInv i (s.procs i)

namespace Origin

variable {i : Fin n} {s : State n Tx} {instr : Instr n Tx}

theorem act (h : Origin i s) (hact : instr.actions i = Algo.step f Δ lead i (s.procs i)) :
    Origin i (s.act instr) := by
  have hprocs : ∀ k c, Msg.vote i c ∈ ((s.act instr).procs k).S →
      Msg.vote i c ∈ ((s.act instr).procs i).S := by
    intro k c hc
    by_cases hk : k = i
    · subst hk; exact hc
    · rw [State.act_procs] at hc ⊢
      have hc' := Processor.mem_S_executeAll_of_signer_ne k _ _ hc
        (by simp [Msg.signer, Ne.symm hk])
      exact Processor.S_subset_executeAll i _ _ (h.procs k c hc')
  refine ⟨hprocs, fun x hx c hxc => ?_⟩
  rcases State.mem_pool_act hx with hx | ⟨k, m, j, hm, rfl, hg⟩
  · rw [State.act_procs]
    exact Processor.S_subset_executeAll i _ _ (h.pool x hx c hxc)
  · simp only at hxc
    subst hxc
    by_cases hk : k = i
    · subst hk
      rw [hact] at hm
      rw [State.act_procs, hact, Algo.executeAll_step]
      exact Algo.mem_S_of_send_step hm
    · rcases hg with hg | hg
      · exact absurd (Option.some.inj hg) (Ne.symm hk)
      · exact hprocs k c hg

theorem step (h : Origin i s) (hact : instr.actions i = Algo.step f Δ lead i (s.procs i)) :
    Origin i (s.step instr) := by
  have ha := h.act hact
  have hsub : ((s.act instr).procs i).S ⊆ ((s.step instr).procs i).S := by
    have := (State.step_procs s instr i).S
    rwa [Processor.tick_S, ← State.act_procs] at this
  refine ⟨fun k c hc => ?_, fun x hx c hxc => ?_⟩
  · rcases State.mem_S_step hc with hc | ⟨x, _, hxp, _, hxm⟩ | ⟨tr, htr⟩
    · exact hsub (ha.procs k c hc)
    · exact hsub (ha.pool x hxp c hxm.symm)
    · cases htr
  · rw [State.step_pool] at hx
    exact hsub (ha.pool x hx c hxc)

end Origin

namespace Inv

variable {i : Fin n} {s : State n Tx} {instr : Instr n Tx}

theorem step (h : Inv i s) (hact : instr.actions i = Algo.step f Δ lead i (s.procs i)) :
    Inv i (s.step instr) := by
  have ha := h.origin.act hact
  refine ⟨h.origin.step hact, ?_⟩
  have hloc : Algo.VoteInv i (((s.procs i).executeAll i (instr.actions i)).tick (s.procs i).S) := by
    rw [hact, Algo.executeAll_step]
    exact (h.vote.stepPair f Δ lead).tick _
  refine hloc.of_sgrows (State.step_procs s instr i) fun c hc => ?_
  rw [Processor.tick_S, ← State.act_procs]
  rcases State.mem_S_step hc with hc | ⟨x, _, hxp, _, hxm⟩ | ⟨tr, htr⟩
  · exact hc
  · exact ha.pool x hxp c hxm.symm
  · cases htr

omit [DecidableEq Tx] in
theorem init (hinit : Init s₀) (i : Fin n) : Inv i s₀ := by
  have hS : ∀ k, (s₀.procs k).S = ∅ := fun k => by rw [hinit.procs k]; rfl
  refine ⟨⟨fun k c hc => ?_, fun x hx => ?_⟩, ⟨?_, fun c hc => ?_, fun c c' hc => ?_⟩⟩
  · rw [hS] at hc; simp at hc
  · rw [hinit.pool] at hx; simp at hx
  · rw [hinit.procs i]; exact le_refl 1
  · rw [hS] at hc; simp at hc
  · rw [hS] at hc; simp at hc

/-- 正直者 p_i について、不変量は全スロットで成り立つ。 -/
theorem run (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) : ∀ t, Inv i (State.run s₀ instrs t)
  | 0 => init hinit i
  | t + 1 => (run hinit hh hi t).step (hh t i (hi t))

end Inv

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

theorem mem_voteSenders {q : Fin n} {b : Block Tx} :
    q ∈ voteSenders instrs b ↔ Sends instrs q (Msg.vote q b) := by
  simp [voteSenders]

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
  exact (Inv.run hinit hh hi (max (t + 1) (t' + 1))).vote.unique b b'
    (S_subset_run s₀ instrs i hle₁ h₁) (S_subset_run s₀ instrs i hle₂ h₂) hview

/-- 正直者が投票するブロックの view は 1 以上。 -/
theorem one_le_view_of_sends (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {b : Block Tx} (hb : Sends instrs i (Msg.vote i b)) :
    1 ≤ b.view.val := by
  obtain ⟨t, j, ht⟩ := hb
  exact ((Inv.run hinit hh hi (t + 1)).vote.notar b (mem_S_succ_of_send hh hi ht)).1

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
