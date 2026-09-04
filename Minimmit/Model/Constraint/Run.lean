import Minimmit.Model.Constraint.Basic
import Minimmit.Model.Algo.Forward
import Mathlib.Data.Fintype.Card

/-!
# 実行の補題

`State.run` に沿って成り立つ事実。前半は正直/腐敗によらない: 署名の偽造不能の帰結（S や
pool にある署名付き message は、その署名者が前に送った）、byz の単調性、定足数の交わり。
後半は正直者について: 局所不変量 `LocalInv`・`PropInv` が全スロットで成り立つこと、
送るブロックは登りの後の `leaderBlock` であること、同じ view のブロックを 2 つ送らないこと。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f : Nat} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-! ### 送信の時刻 -/

/-- p_q がスロット t より前に m を送る。 -/
def SendsBefore (instrs : Nat → Instr n Tx) (q : Fin n) (m : Msg n Tx) (t : Nat) : Prop :=
  ∃ t' < t, ∃ j, Action.send m j ∈ (instrs t').actions q

omit [DecidableEq Tx] in
theorem SendsBefore.sends {q : Fin n} {m : Msg n Tx} {t : Nat} (h : SendsBefore instrs q m t) :
    Sends instrs q m :=
  let ⟨t', _, j, hj⟩ := h; ⟨t', j, hj⟩

omit [DecidableEq Tx] in
theorem SendsBefore.mono {q : Fin n} {m : Msg n Tx} {t t' : Nat} (h : SendsBefore instrs q m t)
    (htt : t ≤ t') : SendsBefore instrs q m t' :=
  let ⟨t₀, ht₀, j, hj⟩ := h; ⟨t₀, lt_of_lt_of_le ht₀ htt, j, hj⟩

/-! ### 署名の偽造不能の帰結 -/

/-- スロット t の S か pool にある、q の署名付きの message は、q が t より前に送った。 -/
theorem sendsBefore_of_mem (hinit : Init s₀) (t : Nat) :
    (∀ k (m : Msg n Tx) q, m ∈ ((State.run s₀ instrs t).procs k).S → m.signer = some q →
      SendsBefore instrs q m t)
    ∧ (∀ x ∈ (State.run s₀ instrs t).pool, ∀ q, x.msg.signer = some q →
      SendsBefore instrs q x.msg t) := by
  induction t with
  | zero =>
    refine ⟨fun k m q hm _ => ?_, fun x hx _ _ => ?_⟩
    · rw [State.run, hinit.procs k] at hm; simp [Processor.init] at hm
    · rw [State.run, hinit.pool] at hx; simp at hx
  | succ t ih =>
    obtain ⟨ihS, ihP⟩ := ih
    have hrun : State.run s₀ instrs (t + 1) = (State.run s₀ instrs t).step (instrs t) := rfl
    -- 動作の後の S
    have hactS : ∀ k (m : Msg n Tx) q,
        m ∈ (((State.run s₀ instrs t).act (instrs t)).procs k).S → m.signer = some q →
        SendsBefore instrs q m (t + 1) := by
      intro k m q hm hq
      rw [State.act_procs] at hm
      by_cases hk : k = q
      · subst hk
        rcases Processor.mem_S_executeAll k _ _ hm with hm | ⟨j, hj⟩
        · exact (ihS k m k hm hq).mono (Nat.le_succ t)
        · exact ⟨t, Nat.lt_succ_self t, j, hj⟩
      · have hm' := Processor.mem_S_executeAll_of_signer_ne k _ _ hm
          (by rw [hq]; exact fun h => hk (Option.some.inj h).symm)
        exact (ihS k m q hm' hq).mono (Nat.le_succ t)
    -- 動作の後の pool
    have hactP : ∀ x ∈ ((State.run s₀ instrs t).act (instrs t)).pool, ∀ q,
        x.msg.signer = some q → SendsBefore instrs q x.msg (t + 1) := by
      intro x hx q hq
      rcases State.mem_pool_act hx with hx | ⟨k, m, j, hm, rfl, hg⟩
      · exact (ihP x hx q hq).mono (Nat.le_succ t)
      · simp only at hq ⊢
        rcases hg with hg | hg
        · rw [hq] at hg
          obtain rfl := Option.some.inj hg
          exact ⟨t, Nat.lt_succ_self t, j, hm⟩
        · exact hactS k m q hg hq
    refine ⟨fun k m q hm hq => ?_, fun x hx q hq => ?_⟩
    · rw [hrun] at hm
      rcases State.mem_S_step hm with hm | ⟨x, _, hxp, _, hxm⟩ | ⟨tr, rfl⟩
      · exact hactS k m q hm hq
      · rw [hxm] at hq ⊢; exact hactP x hxp q hq
      · cases hq
    · rw [hrun, State.step_pool] at hx
      exact hactP x hx q hq

theorem sendsBefore_of_mem_S (hinit : Init s₀) {t : Nat} {k : Fin n} {m : Msg n Tx} {q : Fin n}
    (hm : m ∈ ((State.run s₀ instrs t).procs k).S) (hq : m.signer = some q) :
    SendsBefore instrs q m t :=
  (sendsBefore_of_mem hinit t).1 k m q hm hq

theorem sends_of_mem_S (hinit : Init s₀) {t : Nat} {k : Fin n} {m : Msg n Tx} {q : Fin n}
    (hm : m ∈ ((State.run s₀ instrs t).procs k).S) (hq : m.signer = some q) :
    Sends instrs q m :=
  (sendsBefore_of_mem_S hinit hm hq).sends

/-! ### 腐敗 -/

theorem byz_subset_run (s₀ : State n Tx) (instrs : Nat → Instr n Tx) {t t' : Nat} (h : t ≤ t') :
    (State.run s₀ instrs t).byz ⊆ (State.run s₀ instrs t').byz := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (State.byz_subset_step _ _)

/-- 正直者でなければ、どこかのスロットで腐敗している。 -/
theorem exists_byz_of_not_correct {q : Fin n} (h : ¬ Correct s₀ instrs q) :
    ∃ t, q ∈ (State.run s₀ instrs t).byz := by
  by_contra hne
  exact h fun t ht => hne ⟨t, ht⟩

/-- どこかのスロットで腐敗しているプロセッサの集合は f 人以下。 -/
theorem card_le_of_byz (hb : ByzBound f s₀ instrs) (Q : Finset (Fin n))
    (hQ : ∀ q ∈ Q, ∃ t, q ∈ (State.run s₀ instrs t).byz) : Q.card ≤ f := by
  suffices h : ∃ T, Q ⊆ (State.run s₀ instrs T).byz by
    obtain ⟨T, hT⟩ := h
    exact (Finset.card_le_card hT).trans (hb T)
  induction Q using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | insert q Q _ ih =>
    obtain ⟨T, hT⟩ := ih fun q' hq' => hQ q' (Finset.mem_insert_of_mem hq')
    obtain ⟨t, ht⟩ := hQ q (Finset.mem_insert_self q Q)
    refine ⟨max T t, Finset.insert_subset ?_ ?_⟩
    · exact byz_subset_run s₀ instrs (le_max_right T t) ht
    · exact hT.trans (byz_subset_run s₀ instrs (le_max_left T t))

/-- f 人より多い集合には正直者がいる。 -/
theorem exists_correct_of_lt_card (hb : ByzBound f s₀ instrs) {Q : Finset (Fin n)}
    (hQ : f < Q.card) : ∃ q ∈ Q, Correct s₀ instrs q := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  exact absurd (card_le_of_byz hb Q fun q hq => exists_byz_of_not_correct (hne q hq))
    (not_le.mpr hQ)

/-! ### 定足数の交わり -/

omit [DecidableEq Tx] in
theorem card_inter_add_n_ge (A B : Finset (Fin n)) : A.card + B.card ≤ (A ∩ B).card + n := by
  have h₁ := Finset.card_union_add_card_inter A B
  have h₂ : (A ∪ B).card ≤ n := by
    simpa [Fintype.card_fin] using Finset.card_le_univ (A ∪ B)
  omega

variable {Δ : Nat} {lead : View → Fin n}

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
  refine ⟨⟨le_refl 1, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp [Processor.init]

theorem localInv_step (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) (t : Nat) (h : Algo.LocalInv f i ((State.run s₀ instrs t).procs i)) :
    Algo.LocalInv f i ((State.run s₀ instrs (t + 1)).procs i) := by
  have hact := hh t i (hi t)
  have hloc : Algo.LocalInv f i ((((State.run s₀ instrs t).procs i).executeAll i
      ((instrs t).actions i)).tick) := by
    rw [hact, Algo.executeAll_step]
    exact (h.stepPair Δ lead).tick
  refine hloc.of_sgrows (State.step_procs _ _ i) (fun c hc => ?_) (fun w hw => ?_)
  · rw [Processor.tick_S, ← State.act_procs]; exact own_mem_act_of_mem_succ hinit hh hi rfl hc
  · rw [Processor.tick_S, ← State.act_procs]; exact own_mem_act_of_mem_succ hinit hh hi rfl hw

/-- 正直者 p_i の局所不変量は全スロットで成り立つ。 -/
theorem localInv_run (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) : ∀ t, Algo.LocalInv f i ((State.run s₀ instrs t).procs i)
  | 0 => localInv_init hinit i
  | t + 1 => localInv_step hinit hh hi t (localInv_run hinit hh hi t)

omit [DecidableEq Tx] in
theorem propInv_init (hinit : Init s₀) (i : Fin n) : Algo.PropInv i (s₀.procs i) := by
  rw [hinit.procs i]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Processor.init]

theorem propInv_step (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) (t : Nat) (h : Algo.PropInv i ((State.run s₀ instrs t).procs i)) :
    Algo.PropInv i ((State.run s₀ instrs (t + 1)).procs i) := by
  have hact := hh t i (hi t)
  have hloc : Algo.PropInv i ((((State.run s₀ instrs t).procs i).executeAll i
      ((instrs t).actions i)).tick) := by
    rw [hact, Algo.executeAll_step]
    exact (h.stepPair (f := f) Δ lead).tick
  refine hloc.of_sgrows (State.step_procs _ _ i) fun b hb => ?_
  rw [Processor.tick_S, ← State.act_procs]; exact own_mem_act_of_mem_succ hinit hh hi rfl hb

/-- 正直者 p_i の提案の不変量は全スロットで成り立つ。 -/
theorem propInv_run (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) (t : Nat) : Algo.PropInv i ((State.run s₀ instrs t).procs i) := by
  induction t with
  | zero => exact propInv_init hinit i
  | succ t ih => exact propInv_step hinit hh hi t ih

/-- 正直者がスロット t に送るブロックは、登りの後の状態の `leaderBlock`。 -/
theorem send_block_eq (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {b : Block Tx} {j : Fin n}
    (h : Action.send (Msg.block i b) j ∈ (instrs t).actions i) :
    b = Algo.leaderBlock f (Algo.st1 f i ((State.run s₀ instrs t).procs i))
      ∧ lead (Algo.st1 f i ((State.run s₀ instrs t).procs i)).view = i
      ∧ (Algo.st1 f i ((State.run s₀ instrs t).procs i)).proposed = false := by
  rw [hh t i (hi t), Algo.step_eq_stepPair, Algo.stepPair_snd] at h
  simp only [List.mem_append] at h
  rcases h with (((((h | h) | h) | h) | h) | h)
  · obtain ⟨_, _, hm, _⟩ := Algo.send_climb (localInv_run hinit hh hi t) h
    cases hm
  · obtain ⟨hm, hl, hp⟩ := Algo.send_propose_eq' h
    injection hm with _ hbb
    exact ⟨hbb, hl, hp⟩
  · obtain ⟨_, hm, _⟩ := Algo.send_voteProposal_eq h; cases hm
  · obtain ⟨hm, _⟩ := Algo.send_nullifyTimeout_eq h; cases hm
  · obtain ⟨hm, _⟩ := Algo.send_nullifyNoProgress_eq h; cases hm
  · rw [Algo.forwardNew_eq] at h
    obtain ⟨m', hm', _, hmm⟩ := Algo.mem_disseminateAll_snd.mp h
    cases hmm
    exact absurd hm' Algo.not_block_mem_forwardMsgs

/-- 正直者が同じ view のブロックを 2 つ送ることはない。 -/
theorem leader_block_unique (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t₁ t₂ : Nat} {b₁ b₂ : Block Tx} {j₁ j₂ : Fin n}
    (h₁ : Action.send (Msg.block i b₁) j₁ ∈ (instrs t₁).actions i)
    (h₂ : Action.send (Msg.block i b₂) j₂ ∈ (instrs t₂).actions i) (hv : b₁.view = b₂.view) :
    b₁ = b₂ := by
  -- 同じスロットなら同じブロック。違うスロットなら、先のブロックが S にあって proposed が立つ
  wlog hle : t₁ ≤ t₂ generalizing t₁ t₂ b₁ b₂ j₁ j₂
  · exact (this h₂ h₁ hv.symm (Nat.le_of_not_le hle)).symm
  obtain ⟨hb₁, _, _⟩ := send_block_eq hinit hh hi h₁
  obtain ⟨hb₂, _, hp₂⟩ := send_block_eq hinit hh hi h₂
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · rw [hb₁, hb₂]
  · exfalso
    have hmem : Msg.block i b₁ ∈ ((State.run s₀ instrs t₂).procs i).S :=
      S_subset_run s₀ instrs i hlt (mem_S_succ_of_send hh hi h₁)
    have hP := (propInv_run hinit hh hi t₂).climb (f := f)
      (Algo.maxView ((State.run s₀ instrs t₂).procs i).S + 1)
    have hmem1 : Msg.block i b₁ ∈ (Algo.st1 f i ((State.run s₀ instrs t₂).procs i)).S :=
      Algo.S_subset_st1 f i _ hmem
    have hv1 : b₁.view = (Algo.st1 f i ((State.run s₀ instrs t₂).procs i)).view := by
      rw [hv, hb₂]; rfl
    have := hP.prop_flag b₁ hmem1 hv1
    have h' : (Algo.st1 f i ((State.run s₀ instrs t₂).procs i)).proposed = true := this
    rw [hp₂] at h'; cases h'

omit [DecidableEq Tx] in
theorem mem_voteSenders {q : Fin n} {b : Block Tx} :
    q ∈ voteSenders instrs b ↔ Sends instrs q (Msg.vote q b) := by
  simp [voteSenders]

omit [DecidableEq Tx] in
theorem mem_nullifySenders {q : Fin n} {v : View} :
    q ∈ nullifySenders instrs v ↔ Sends instrs q (Msg.nullify q v) := by
  simp [nullifySenders]

end Minimmit
