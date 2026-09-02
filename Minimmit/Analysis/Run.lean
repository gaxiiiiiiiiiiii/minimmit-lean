import Minimmit.Model.Constraint
import Minimmit.Analysis.Algo
import Mathlib.Data.Fintype.Card

/-!
# 実行の補題

`State.run` に沿って成り立つ、正直/腐敗によらない事実。署名の偽造不能の帰結（S や pool に
ある署名付き message は、その署名者が前に送った）、byz の単調性、定足数の交わり。
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

/-- 正直者でなければ、いつか腐敗する。 -/
theorem exists_byz_of_not_correct {q : Fin n} (h : ¬ Correct s₀ instrs q) :
    ∃ t, q ∈ (State.run s₀ instrs t).byz := by
  by_contra hne
  exact h fun t ht => hne ⟨t, ht⟩

/-- いつか腐敗するプロセッサの集合は f 人以下。 -/
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

end Minimmit
