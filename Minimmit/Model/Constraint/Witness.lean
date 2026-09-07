import Minimmit.Model.Constraint.Basic
import Minimmit.Model.Constraint.Run
import Minimmit.Model.Transition.Execute

/-!
# 制約の充足可能性

`Init`・`Honest`・`ByzBound`・`PartialSync` を同時に満たす実行の例。腐敗がなく、全員が
`Algo.step` に従い、送った packet がそのスロットのうちに届く実行を、スロットの冒頭の状態から
そのスロットの指示を作る再帰で定義する。§5 の補題の仮定が矛盾しないことを
`constraints_satisfiable` として示す。あわせて、論文の輪番のリーダー関数が `Fair` を満たすことを
`roundRobin_fair` として、Lemma 5.10 のリーダーの仮定を満たすことを `roundRobin_correct_leader`
として示す。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Witness

/-- 初期状態: 全員 `Processor.init`、byz と pool は空、now は 0。 -/
def init : State n Tx :=
  { procs := fun _ => Processor.init, byz := ∅, pool := ∅, now := ⟨0⟩ }

/-- 状態 s を冒頭とするスロットの指示: 全員の動作は `Algo.step` の出力、配送は動作の後の pool
    にある packet 全部、取引の投入と腐敗はなし。 -/
noncomputable def instrOf (f Δ : Nat) (lead : View → Fin n) (s : State n Tx) : Instr n Tx :=
  let acts : Instr n Tx :=
    { actions := fun i => Algo.step f Δ lead i (s.procs i), deliveries := [], submits := [],
      corrupts := [] }
  { acts with deliveries := (s.act acts).pool.toList }

@[simp] theorem instrOf_actions (f Δ : Nat) (lead : View → Fin n) (s : State n Tx) (i : Fin n) :
    (instrOf f Δ lead s).actions i = Algo.step f Δ lead i (s.procs i) := rfl

@[simp] theorem instrOf_submits (f Δ : Nat) (lead : View → Fin n) (s : State n Tx) :
    (instrOf f Δ lead s).submits = [] := rfl

@[simp] theorem instrOf_corrupts (f Δ : Nat) (lead : View → Fin n) (s : State n Tx) :
    (instrOf f Δ lead s).corrupts = [] := rfl

theorem instrOf_deliveries (f Δ : Nat) (lead : View → Fin n) (s : State n Tx) :
    (instrOf f Δ lead s).deliveries = (s.act (instrOf f Δ lead s)).pool.toList := rfl

/-- スロット t の冒頭の状態と、そのスロットの指示の対 -/
noncomputable def trace (f Δ : Nat) (lead : View → Fin n) : Nat → State n Tx × Instr n Tx
  | 0 => (init, instrOf f Δ lead init)
  | t + 1 =>
    let s := (trace f Δ lead t).1.step (trace f Δ lead t).2
    (s, instrOf f Δ lead s)

/-- 指示の列、`trace` の指示成分 -/
noncomputable def instrs (f Δ : Nat) (lead : View → Fin n) (t : Nat) : Instr n Tx :=
  (trace (Tx := Tx) f Δ lead t).2

theorem trace_snd (f Δ : Nat) (lead : View → Fin n) (t : Nat) :
    (trace (Tx := Tx) f Δ lead t).2 = instrOf f Δ lead (trace f Δ lead t).1 := by
  cases t <;> rfl

/-- 実行は `trace` の状態成分。 -/
theorem run_eq (f Δ : Nat) (lead : View → Fin n) (t : Nat) :
    State.run (init (Tx := Tx)) (instrs f Δ lead) t = (trace f Δ lead t).1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [State.run, ih]; rfl

theorem init_spec : Init (init (n := n) (Tx := Tx)) :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

theorem honest (f Δ : Nat) (lead : View → Fin n) :
    Honest f Δ lead (init (Tx := Tx)) (instrs f Δ lead) := by
  intro t i _
  rw [run_eq, instrs, trace_snd, instrOf_actions]

theorem byz_eq (f Δ : Nat) (lead : View → Fin n) (t : Nat) :
    (trace (Tx := Tx) f Δ lead t).1.byz = ∅ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change ((trace (Tx := Tx) f Δ lead t).1.step (trace f Δ lead t).2).byz = ∅
    rw [State.step_eq, trace_snd, instrOf_corrupts, instrOf_submits, List.foldl_nil,
      List.foldl_nil, State.foldl_deliver_byz, State.tick_byz, State.act_byz, ih]

theorem byzBound (f Δ : Nat) (lead : View → Fin n) :
    ByzBound f (init (Tx := Tx)) (instrs f Δ lead) := by
  intro t
  rw [run_eq, byz_eq, Finset.card_empty]
  exact Nat.zero_le _

/-- pool にある packet を全部配送すると、各 packet の message は宛先の S にある。 -/
theorem mem_S_foldl_deliver_of_mem (s : State n Tx) (xs : List (Packet n Tx)) {x : Packet n Tx}
    (hx : x ∈ xs) (hp : x ∈ s.pool) : x.msg ∈ ((xs.foldl State.deliver s).procs x.dst).S := by
  induction xs generalizing s with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with hxy | hx
    · subst hxy
      refine (State.foldl_deliver_sgrows _ ys _).S ?_
      rw [State.deliver, if_pos hp, State.update_procs_self, Processor.receive_S]
      exact Finset.mem_insert_self _ _
    · exact ih _ hx (by rwa [State.deliver_pool])

/-- 各スロットの冒頭で、pool にある packet の message は宛先の S にある。 -/
theorem pool_delivered (f Δ : Nat) (lead : View → Fin n) (t : Nat) :
    ∀ x ∈ (trace (Tx := Tx) f Δ lead t).1.pool, x.msg ∈ ((trace f Δ lead t).1.procs x.dst).S := by
  intro x hx
  cases t with
  | zero => simp [trace, init] at hx
  | succ t =>
    change x ∈ ((trace (Tx := Tx) f Δ lead t).1.step (trace f Δ lead t).2).pool at hx
    change x.msg ∈ (((trace (Tx := Tx) f Δ lead t).1.step (trace f Δ lead t).2).procs x.dst).S
    rw [State.step_pool, trace_snd] at hx
    rw [State.step_eq, trace_snd, instrOf_corrupts, instrOf_submits, List.foldl_nil,
      List.foldl_nil, instrOf_deliveries]
    exact mem_S_foldl_deliver_of_mem _ _ (Finset.mem_toList.mpr hx) (by rwa [State.tick_pool])

/-- 部分同期: GST = 0 で、期限によらず届いている。 -/
theorem partialSync (f Δ : Nat) (lead : View → Fin n) (hΔ : 1 ≤ Δ) :
    PartialSync Δ ⟨0⟩ (init (Tx := Tx)) (instrs f Δ lead) where
  timely := fun t x hx _ => by
    rw [run_eq] at hx ⊢
    exact pool_delivered f Δ lead t x hx
  one_le := hΔ

end Witness

/-- `Init`・`Honest`・`ByzBound`・`PartialSync` は同時に満たせる: Δ ≥ 1 なら、どの f・lead についても
    4 つを満たす初期状態と指示の列がある。 -/
theorem constraints_satisfiable (f Δ : Nat) (hΔ : 1 ≤ Δ) (lead : View → Fin n) :
    ∃ (s₀ : State n Tx) (instrs : Nat → Instr n Tx),
      Init s₀ ∧ Honest f Δ lead s₀ instrs ∧ ByzBound f s₀ instrs
        ∧ ∃ GST, PartialSync Δ GST s₀ instrs :=
  ⟨Witness.init, Witness.instrs f Δ lead, Witness.init_spec, Witness.honest f Δ lead,
    Witness.byzBound f Δ lead, ⟨⟨0⟩, Witness.partialSync f Δ lead hΔ⟩⟩

/-! ### 輪番のリーダー -/

/-- 論文の輪番 lead(v) = p_{(v mod n)+1}、添字を 0 始まりにして v mod n -/
def roundRobin (hn : 0 < n) (v : View) : Fin n := ⟨v.val % n, Nat.mod_lt _ hn⟩

theorem roundRobin_fair (hn : 0 < n) : Fair (roundRobin hn) := by
  intro i v
  refine ⟨⟨i.val + (v.val / n + 1) * n⟩, ?_, ?_⟩
  · have h := Nat.lt_div_mul_add (a := v.val) hn
    show v.val ≤ i.val + (v.val / n + 1) * n
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · apply Fin.ext
    show (i.val + (v.val / n + 1) * n) % n = i.val
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

/-- 論文の輪番は、腐敗が fa 人以下で fa + 1 ≤ n なら、どの fa + 1 個の連続する view にも正直な
    リーダーを持つ（Lemma 5.10 のリーダーの仮定）。 -/
theorem roundRobin_correct_leader {s₀ : State n Tx} {instrs : Nat → Instr n Tx} (hn : 0 < n)
    {fa : Nat} (hfa : fa + 1 ≤ n) (hb : ByzBound fa s₀ instrs) :
    CorrectLeaderWithin s₀ instrs (roundRobin hn) fa := by
  classical
  intro v
  -- view v〜v + fa のリーダーは相異なる fa + 1 人なので、正直者がいる
  have hinj : Set.InjOn (fun k => roundRobin hn ⟨v.val + k⟩) ↑(Finset.range (fa + 1)) := by
    intro k₁ hk₁ k₂ hk₂ h
    rw [Finset.mem_coe, Finset.mem_range] at hk₁ hk₂
    have h' : (v.val + k₁) % n = (v.val + k₂) % n := congrArg Fin.val h
    rcases le_total k₁ k₂ with hle | hle
    · have h0 := Nat.sub_mod_eq_zero_of_mod_eq h'.symm
      rw [Nat.add_sub_add_left, Nat.mod_eq_of_lt (by omega)] at h0
      omega
    · have h0 := Nat.sub_mod_eq_zero_of_mod_eq h'
      rw [Nat.add_sub_add_left, Nat.mod_eq_of_lt (by omega)] at h0
      omega
  have hcard : fa < ((Finset.range (fa + 1)).image fun k => roundRobin hn ⟨v.val + k⟩).card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]; exact Nat.lt_succ_self fa
  obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb hcard
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  have hk := Finset.mem_range.mp hk
  exact ⟨⟨v.val + k⟩, Nat.le_add_right _ _, by show v.val + k ≤ v.val + fa; omega, hqc⟩

end Minimmit
