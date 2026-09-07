import Minimmit.Model.Constraint.Basic
import Minimmit.Model.Algo.Forward
import Mathlib.Data.Fintype.Card

/-!
# 実行の補題

`State.run` に沿って成り立つ事実。前半は正直/腐敗によらない: 署名の偽造不能の帰結（S や
pool にある署名付き message は、その署名者が前に送った。S や pool が含む署名付きブロックは、
その署名者が前に送った message の成分）、byz の単調性、定足数の交わり。
後半は正直者について: 局所不変量 `LocalInv`・`PropInv` が全スロットで成り立つこと、
送るブロックは登りの後の `leaderBlock` であること、自分の署名付きのブロックは自分の S に
含まれること、同じ view の自分の署名付きのブロックは 1 つしかないこと。
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

/-- p_q がスロット t より前に、b を成分に持つ message を送る。 -/
def SendsBlockBefore (instrs : Nat → Instr n Tx) (q : Fin n) (b : Block n Tx) (t : Nat) : Prop :=
  ∃ t' < t, ∃ m j, m.block = some b ∧ Action.send m j ∈ (instrs t').actions q

omit [DecidableEq Tx] in
theorem SendsBlockBefore.mono {q : Fin n} {b : Block n Tx} {t t' : Nat}
    (h : SendsBlockBefore instrs q b t) (htt : t ≤ t') : SendsBlockBefore instrs q b t' :=
  let ⟨t₀, ht₀, m, j, hm, hj⟩ := h; ⟨t₀, lt_of_lt_of_le ht₀ htt, m, j, hm, hj⟩

/-- スロット t の S か pool が含む、q の署名付きのブロックは、q が t より前に送った message の
    成分。 -/
theorem sendsBlockBefore_of_containsBlock (hinit : Init s₀) (t : Nat) :
    (∀ k (b : Block n Tx) q, containsBlock ((State.run s₀ instrs t).procs k).S b →
      b.signer = some q → SendsBlockBefore instrs q b t)
    ∧ (∀ x ∈ (State.run s₀ instrs t).pool, ∀ (b : Block n Tx) q, x.msg.block = some b →
      b.signer = some q → SendsBlockBefore instrs q b t) := by
  induction t with
  | zero =>
    refine ⟨fun k b q hb _ => ?_, fun x hx _ _ _ _ => ?_⟩
    · obtain ⟨m, hm, _⟩ := hb
      rw [State.run, hinit.procs k] at hm; simp [Processor.init] at hm
    · rw [State.run, hinit.pool] at hx; simp at hx
  | succ t ih =>
    obtain ⟨ihS, ihP⟩ := ih
    have hrun : State.run s₀ instrs (t + 1) = (State.run s₀ instrs t).step (instrs t) := rfl
    -- 動作の後の S
    have hactS : ∀ k (b : Block n Tx) q,
        containsBlock (((State.run s₀ instrs t).act (instrs t)).procs k).S b →
        b.signer = some q → SendsBlockBefore instrs q b (t + 1) := by
      intro k b q hb hq
      rw [State.act_procs] at hb
      rcases Processor.containsBlock_executeAll k _ _ hb with hb | ⟨hk, m, j, hmb, hj⟩
      · exact (ihS k b q hb hq).mono (Nat.le_succ t)
      · rw [hq] at hk
        obtain rfl := Option.some.inj hk
        exact ⟨t, Nat.lt_succ_self t, m, j, hmb, hj⟩
    -- 動作の後の pool
    have hactP : ∀ x ∈ ((State.run s₀ instrs t).act (instrs t)).pool, ∀ (b : Block n Tx) q,
        x.msg.block = some b → b.signer = some q → SendsBlockBefore instrs q b (t + 1) := by
      intro x hx b q hb hq
      rcases State.mem_pool_act hx with hx | ⟨k, m, j, hm, rfl, hg⟩
      · exact (ihP x hx b q hb hq).mono (Nat.le_succ t)
      · simp only at hb
        have hok : b.signer = some k
            ∨ containsBlock (((State.run s₀ instrs t).act (instrs t)).procs k).S b := by
          have := hg.2; rwa [hb] at this
        rcases hok with hk | hc
        · rw [hq] at hk
          obtain rfl := Option.some.inj hk
          exact ⟨t, Nat.lt_succ_self t, m, j, hb, hm⟩
        · exact hactS k b q hc hq
    refine ⟨fun k b q hb hq => ?_, fun x hx b q hb hq => ?_⟩
    · obtain ⟨m, hm, hmb⟩ := hb
      rw [hrun] at hm
      rcases State.mem_S_step hm with hm | ⟨x, _, hxp, _, hxm⟩ | ⟨tr, rfl⟩
      · exact hactS k b q ⟨m, hm, hmb⟩ hq
      · rw [hxm] at hmb; exact hactP x hxp b q hmb hq
      · cases hmb
    · rw [hrun, State.step_pool] at hx
      exact hactP x hx b q hb hq

theorem sendsBlockBefore_of_containsBlock_S (hinit : Init s₀) {t : Nat} {k : Fin n}
    {b : Block n Tx} {q : Fin n} (hb : containsBlock ((State.run s₀ instrs t).procs k).S b)
    (hq : b.signer = some q) : SendsBlockBefore instrs q b t :=
  (sendsBlockBefore_of_containsBlock hinit t).1 k b q hb hq

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

/-- 正直者 p_i がスロット t に送った message の成分のブロックは、スロット t + 1 の S に含まれる。 -/
theorem containsBlock_succ_of_send (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {m : Msg n Tx} {j : Fin n} {b : Block n Tx}
    (h : Action.send m j ∈ (instrs t).actions i) (hmb : m.block = some b) :
    containsBlock ((State.run s₀ instrs (t + 1)).procs i).S b :=
  ⟨m, mem_S_succ_of_send hh hi h, hmb⟩

/-- 正直者 p_i の署名付きのブロックがスロット t + 1 の S に含まれれば、スロット t の動作の後の
    S に既に含まれる。配送で初めて入ることはない。 -/
theorem own_containsBlock_act_of_succ (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    {i : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {b : Block n Tx} (hb : b.signer = some i)
    (h : containsBlock ((State.run s₀ instrs (t + 1)).procs i).S b) :
    containsBlock (((State.run s₀ instrs t).act (instrs t)).procs i).S b := by
  obtain ⟨t', ht', m, j, hmb, hj⟩ := sendsBlockBefore_of_containsBlock_S hinit h hb
  refine ⟨m, ?_, hmb⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
  · have hmem := mem_S_succ_of_send hh hi hj
    have hsub := S_subset_run s₀ instrs i (Nat.succ_le_of_lt ht')
    rw [State.act_procs]
    exact Processor.S_subset_executeAll i _ _ (hsub hmem)
  · have hact := hh t' i (hi t')
    rw [State.act_procs, hact, Algo.executeAll_step]
    rw [hact] at hj
    exact Algo.mem_S_of_send_step hj

/-- 正直者 p_i の署名付きのブロックは、どのプロセッサの S に含まれていても、同じスロットの p_i
    自身の S に含まれる。 -/
theorem own_containsBlock_of_containsBlock (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    {i : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {k : Fin n} {b : Block n Tx}
    (hb : b.signer = some i) (h : containsBlock ((State.run s₀ instrs t).procs k).S b) :
    containsBlock ((State.run s₀ instrs t).procs i).S b := by
  obtain ⟨t', ht', m, j, hmb, hj⟩ := sendsBlockBefore_of_containsBlock_S hinit h hb
  exact ⟨m, S_subset_run s₀ instrs i (Nat.succ_le_of_lt ht') (mem_S_succ_of_send hh hi hj), hmb⟩

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

theorem propInv_init (hinit : Init s₀) (i : Fin n) : Algo.PropInv i (s₀.procs i) := by
  rw [hinit.procs i]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Processor.init, Algo.OwnBlock, containsBlock]

theorem propInv_step (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) (t : Nat) (h : Algo.PropInv i ((State.run s₀ instrs t).procs i)) :
    Algo.PropInv i ((State.run s₀ instrs (t + 1)).procs i) := by
  have hact := hh t i (hi t)
  have hloc : Algo.PropInv i ((((State.run s₀ instrs t).procs i).executeAll i
      ((instrs t).actions i)).tick) := by
    rw [hact, Algo.executeAll_step]
    exact (h.stepPair (f := f) Δ lead).tick
  refine hloc.of_sgrows (State.step_procs _ _ i) fun b ⟨hs, hb⟩ => ⟨hs, ?_⟩
  rw [Processor.tick_S, ← State.act_procs]; exact own_containsBlock_act_of_succ hinit hh hi hs hb

/-- 正直者 p_i の提案の不変量は全スロットで成り立つ。 -/
theorem propInv_run (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) (t : Nat) : Algo.PropInv i ((State.run s₀ instrs t).procs i) := by
  induction t with
  | zero => exact propInv_init hinit i
  | succ t ih => exact propInv_step hinit hh hi t ih

/-- 正直者がスロット t に送るブロックは、登りの後の状態の `leaderBlock`。 -/
theorem send_propose_leaderBlock (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {b : Block n Tx} {j : Fin n}
    (h : Action.send (Msg.propose b) j ∈ (instrs t).actions i) :
    b = Algo.leaderBlock f i (Algo.st1 f i ((State.run s₀ instrs t).procs i))
      ∧ lead (Algo.st1 f i ((State.run s₀ instrs t).procs i)).view = i
      ∧ (Algo.st1 f i ((State.run s₀ instrs t).procs i)).proposed = false := by
  rw [hh t i (hi t), Algo.step_eq_stepPair, Algo.stepPair_snd] at h
  simp only [List.mem_append] at h
  rcases h with (((((h | h) | h) | h) | h) | h)
  · obtain ⟨_, _, hm, _⟩ := Algo.send_climb (localInv_run hinit hh hi t) h
    cases hm
  · obtain ⟨hm, hl, hp⟩ := Algo.send_propose_eq' h
    injection hm with hbb
    exact ⟨hbb, hl, hp⟩
  · obtain ⟨_, hm, _⟩ := Algo.send_voteProposal_eq h; cases hm
  · obtain ⟨hm, _⟩ := Algo.send_nullifyTimeout_eq h; cases hm
  · obtain ⟨hm, _⟩ := Algo.send_nullifyNoProgress_eq h; cases hm
  · rw [Algo.forwardNew_eq] at h
    obtain ⟨m', hm', _, hmm⟩ := Algo.mem_disseminateAll_snd.mp h
    cases hmm
    exact absurd hm' Algo.not_propose_mem_forwardMsgs

/-- 正直者 p_i の署名付きのブロックがどこかの S に含まれるなら、その view は同じスロットの p_i の
    view 以下。 -/
theorem own_block_view_le (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {k : Fin n} {b : Block n Tx} (hb : b.signer = some i)
    (h : containsBlock ((State.run s₀ instrs t).procs k).S b) :
    b.view.val ≤ ((State.run s₀ instrs t).procs i).view.val :=
  (propInv_run hinit hh hi t).prop_view b ⟨hb, own_containsBlock_of_containsBlock hinit hh hi hb h⟩

/-- 正直者 p_i の署名付きで view が同じ 2 つのブロックが、それぞれどこかの S に含まれるなら
    一致する。 -/
theorem own_block_unique (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t₁ t₂ : Nat} {k₁ k₂ : Fin n} {b₁ b₂ : Block n Tx}
    (h₁ : containsBlock ((State.run s₀ instrs t₁).procs k₁).S b₁)
    (h₂ : containsBlock ((State.run s₀ instrs t₂).procs k₂).S b₂)
    (hs₁ : b₁.signer = some i) (hs₂ : b₂.signer = some i) (hv : b₁.view = b₂.view) : b₁ = b₂ := by
  wlog hle : t₁ ≤ t₂ generalizing t₁ t₂ k₁ k₂ b₁ b₂
  · exact (this h₂ h₁ hs₂ hs₁ hv.symm (Nat.le_of_not_le hle)).symm
  have h₁' := own_containsBlock_of_containsBlock hinit hh hi hs₁ h₁
  have h₂' := own_containsBlock_of_containsBlock hinit hh hi hs₂ h₂
  exact (propInv_run hinit hh hi t₂).prop_unique b₁ b₂
    ⟨hs₁, containsBlock_mono (S_subset_run s₀ instrs i hle) h₁'⟩ ⟨hs₂, h₂'⟩ hv

/-- 正直者 p_i の署名付きのブロックがどこかの S に含まれ、p_i が同じ view のブロックを送るなら、
    両者は一致する。 -/
theorem own_block_eq_of_send (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t t' : Nat} {k : Fin n} {b b' : Block n Tx} {j : Fin n}
    (hb : containsBlock ((State.run s₀ instrs t).procs k).S b) (hs : b.signer = some i)
    (h' : Action.send (Msg.propose b') j ∈ (instrs t').actions i) (hv : b.view = b'.view) :
    b = b' := by
  obtain ⟨hb', _, _⟩ := send_propose_leaderBlock hinit hh hi h'
  exact own_block_unique hinit hh hi hb (containsBlock_succ_of_send hh hi h' rfl) hs
    (by rw [hb']; rfl) hv

omit [DecidableEq Tx] in
theorem mem_voteSenders {q : Fin n} {b : Block n Tx} :
    q ∈ voteSenders instrs b ↔ Sends instrs q (Msg.vote q b) := by
  simp [voteSenders]

omit [DecidableEq Tx] in
theorem mem_nullifySenders {q : Fin n} {v : View} :
    q ∈ nullifySenders instrs v ↔ Sends instrs q (Msg.nullify q v) := by
  simp [nullifySenders]

end Minimmit
