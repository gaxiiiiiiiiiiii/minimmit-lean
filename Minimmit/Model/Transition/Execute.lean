import Minimmit.Model.Transition.Basic

/-!
# 遷移系の補題

`State.step` を各プロセッサの局所状態に射影する。p_i の局所状態は、i 自身の動作を
`Processor.execute` で畳み込み、tick で timer と prevS を更新し、配送と取引で S が増える。
他のプロセッサの動作と腐敗は p_i の局所状態を変えない。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type}

namespace Processor

/-! ### tick -/

@[simp] theorem tick_view (p : Processor n Tx) : p.tick.view = p.view := rfl
@[simp] theorem tick_timer (p : Processor n Tx) :
    p.tick.timer = p.timer + 1 := rfl
@[simp] theorem tick_nullified (p : Processor n Tx) :
    p.tick.nullified = p.nullified := rfl
@[simp] theorem tick_proposed (p : Processor n Tx) :
    p.tick.proposed = p.proposed := rfl
@[simp] theorem tick_notarised (p : Processor n Tx) :
    p.tick.notarised = p.notarised := rfl
@[simp] theorem tick_S (p : Processor n Tx) : p.tick.S = p.S := rfl
@[simp] theorem tick_prevS (p : Processor n Tx) : p.tick.prevS = p.S := rfl

/-! ### S だけが増える関係 -/

/-- q から p へ、S が増える以外は変わらない。配送・取引が局所状態に与える効果はこの形。 -/
structure SGrows (q p : Processor n Tx) : Prop where
  view : p.view = q.view
  timer : p.timer = q.timer
  nullified : p.nullified = q.nullified
  proposed : p.proposed = q.proposed
  notarised : p.notarised = q.notarised
  prevS : p.prevS = q.prevS
  S : q.S ⊆ p.S

theorem SGrows.refl (p : Processor n Tx) : p.SGrows p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Finset.Subset.refl _⟩

theorem SGrows.trans {p q r : Processor n Tx} (h₁ : p.SGrows q) (h₂ : q.SGrows r) : p.SGrows r :=
  ⟨h₂.view.trans h₁.view, h₂.timer.trans h₁.timer, h₂.nullified.trans h₁.nullified,
   h₂.proposed.trans h₁.proposed, h₂.notarised.trans h₁.notarised, h₂.prevS.trans h₁.prevS,
   h₁.S.trans h₂.S⟩

variable [DecidableEq Tx]

theorem SGrows.receive (p : Processor n Tx) (m : Msg n Tx) : p.SGrows (p.receive m) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Finset.subset_insert _ _⟩

/-- 動作 a の局所効果: `State.execute` が procs i に与える効果と一致する。send には
    `State.send` と同じガードが付く。 -/
def execute (i : Fin n) (p : Processor n Tx) : Action n Tx → Processor n Tx
  | .send m j => if m.signer = some i ∨ m ∈ p.S then p.send i m j else p
  | .progress => p.progress

/-- 動作の列の局所効果 -/
def executeAll (i : Fin n) (p : Processor n Tx) (acts : List (Action n Tx)) : Processor n Tx :=
  acts.foldl (fun p a => p.execute i a) p

@[simp] theorem executeAll_nil (i : Fin n) (p : Processor n Tx) : p.executeAll i [] = p := rfl

@[simp] theorem executeAll_cons (i : Fin n) (p : Processor n Tx) (a : Action n Tx)
    (acts : List (Action n Tx)) : p.executeAll i (a :: acts) = (p.execute i a).executeAll i acts :=
  rfl

theorem executeAll_append (i : Fin n) (p : Processor n Tx) (l₁ l₂ : List (Action n Tx)) :
    p.executeAll i (l₁ ++ l₂) = (p.executeAll i l₁).executeAll i l₂ := by
  simp [executeAll, List.foldl_append]

theorem S_subset_send (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n) :
    p.S ⊆ (p.send i m j).S := by
  cases m <;> simp only [send] <;> split_ifs <;>
    first | exact Finset.Subset.refl _ | exact Finset.subset_insert _ _

theorem S_subset_execute (i : Fin n) (p : Processor n Tx) (a : Action n Tx) :
    p.S ⊆ (p.execute i a).S := by
  cases a with
  | send m j =>
    simp only [execute]
    split_ifs
    · exact S_subset_send i p m j
    · exact Finset.Subset.refl _
  | progress => exact Finset.Subset.refl _

theorem S_subset_executeAll (i : Fin n) (p : Processor n Tx) (acts : List (Action n Tx)) :
    p.S ⊆ (p.executeAll i acts).S := by
  induction acts generalizing p with
  | nil => exact Finset.Subset.refl _
  | cons a acts ih => exact (S_subset_execute i p a).trans (ih _)

/-! ### send の効果 -/

@[simp] theorem send_view (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n) :
    (p.send i m j).view = p.view := by
  cases m <;> simp only [send] <;> split_ifs <;> rfl

@[simp] theorem send_timer (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n) :
    (p.send i m j).timer = p.timer := by
  cases m <;> simp only [send] <;> split_ifs <;> rfl

@[simp] theorem send_prevS (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n) :
    (p.send i m j).prevS = p.prevS := by
  cases m <;> simp only [send] <;> split_ifs <;> rfl

theorem send_S (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n) :
    (p.send i m j).S = if j = i then insert m p.S else p.S := by
  cases m <;> simp only [send] <;> split_ifs <;> rfl

/-- 自分の現在の view の票でなければ notarised は変わらない。 -/
theorem send_notarised_of_not_vote (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n)
    (h : ∀ b, m = .vote i b → b.view ≠ p.view) : (p.send i m j).notarised = p.notarised := by
  cases m with
  | vote q b =>
    simp only [send]
    have : ¬ (q = i ∧ b.view = p.view) := fun ⟨hq, hb⟩ => h b (by rw [hq]) hb
    simp only [this, if_false]
    split_ifs <;> rfl
  | _ => simp only [send]; split_ifs <;> rfl

theorem send_vote_notarised (i : Fin n) (p : Processor n Tx) (b : Block Tx) (j : Fin n) :
    (p.send i (.vote i b) j).notarised = if b.view = p.view then some b else p.notarised := by
  simp only [send, true_and]
  split_ifs <;> rfl

/-- 自分の現在の view の nullify でなければ nullified は変わらない。 -/
theorem send_nullified_of_not_nullify (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n)
    (h : ∀ v, m = .nullify i v → v ≠ p.view) : (p.send i m j).nullified = p.nullified := by
  cases m with
  | nullify q v =>
    simp only [send]
    have : ¬ (q = i ∧ v = p.view) := fun ⟨hq, hv⟩ => h v (by rw [hq]) hv
    simp only [this, if_false]
    split_ifs <;> rfl
  | _ => simp only [send]; split_ifs <;> rfl

theorem send_nullify_nullified (i : Fin n) (p : Processor n Tx) (v : View) (j : Fin n) :
    (p.send i (.nullify i v) j).nullified = if v = p.view then true else p.nullified := by
  simp only [send, true_and]
  split_ifs <;> rfl

/-- 自分の現在の view のブロックでなければ proposed は変わらない。 -/
theorem send_proposed_of_not_propose (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n)
    (h : ∀ b, m = .propose i b → b.view ≠ p.view) : (p.send i m j).proposed = p.proposed := by
  cases m with
  | propose q b =>
    simp only [send]
    have : ¬ (q = i ∧ b.view = p.view) := fun ⟨hq, hb⟩ => h b (by rw [hq]) hb
    simp only [this, if_false]
    split_ifs <;> rfl
  | _ => simp only [send]; split_ifs <;> rfl

theorem send_propose_proposed (i : Fin n) (p : Processor n Tx) (b : Block Tx) (j : Fin n) :
    (p.send i (.propose i b) j).proposed = if b.view = p.view then true else p.proposed := by
  simp only [send, true_and]
  split_ifs <;> rfl

/-- 署名者が k でない message が k の動作の後に S にあるなら、動作の前からあった。 -/
theorem mem_S_executeAll_of_signer_ne (k : Fin n) (p : Processor n Tx) (acts : List (Action n Tx))
    {m : Msg n Tx} (hm : m ∈ (p.executeAll k acts).S) (hs : m.signer ≠ some k) : m ∈ p.S := by
  induction acts generalizing p with
  | nil => exact hm
  | cons a acts ih =>
    rw [executeAll_cons] at hm
    have h := ih _ hm
    cases a with
    | send m' j =>
      simp only [execute] at h
      split_ifs at h with hg
      · rw [send_S] at h
        split_ifs at h with hj
        · rcases Finset.mem_insert.mp h with rfl | h
          · rcases hg with hg | hg
            · exact absurd hg hs
            · exact hg
          · exact h
        · exact h
      · exact h
    | progress => exact h

/-- k の動作の後に S にある message は、前からあったか、k がこの動作の列で送ったもの。 -/
theorem mem_S_executeAll (k : Fin n) (p : Processor n Tx) (acts : List (Action n Tx))
    {m : Msg n Tx} (hm : m ∈ (p.executeAll k acts).S) :
    m ∈ p.S ∨ ∃ j, Action.send m j ∈ acts := by
  induction acts generalizing p with
  | nil => exact Or.inl hm
  | cons a acts ih =>
    rw [executeAll_cons] at hm
    rcases ih _ hm with h | ⟨j, hj⟩
    · cases a with
      | send m' j' =>
        simp only [execute] at h
        split_ifs at h
        · rw [send_S] at h
          split_ifs at h
          · rcases Finset.mem_insert.mp h with rfl | h
            · exact Or.inr ⟨j', List.mem_cons_self ..⟩
            · exact Or.inl h
          · exact Or.inl h
        · exact Or.inl h
      | progress => exact Or.inl h
    · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj⟩

/-! ### receive は S 以外を変えない -/

@[simp] theorem receive_view (p : Processor n Tx) (m : Msg n Tx) :
    (p.receive m).view = p.view := rfl
@[simp] theorem receive_timer (p : Processor n Tx) (m : Msg n Tx) :
    (p.receive m).timer = p.timer := rfl
@[simp] theorem receive_nullified (p : Processor n Tx) (m : Msg n Tx) :
    (p.receive m).nullified = p.nullified := rfl
@[simp] theorem receive_proposed (p : Processor n Tx) (m : Msg n Tx) :
    (p.receive m).proposed = p.proposed := rfl
@[simp] theorem receive_notarised (p : Processor n Tx) (m : Msg n Tx) :
    (p.receive m).notarised = p.notarised := rfl
@[simp] theorem receive_prevS (p : Processor n Tx) (m : Msg n Tx) :
    (p.receive m).prevS = p.prevS := rfl
@[simp] theorem receive_S (p : Processor n Tx) (m : Msg n Tx) :
    (p.receive m).S = insert m p.S := rfl

theorem S_subset_receive (p : Processor n Tx) (m : Msg n Tx) : p.S ⊆ (p.receive m).S :=
  Finset.subset_insert _ _

end Processor

namespace State

/-! ### update と corrupt -/

theorem corrupt_procs (s : State n Tx) (k : Fin n) : (s.corrupt k).procs = s.procs := rfl

@[simp] theorem update_procs_self (s : State n Tx) (i : Fin n)
    (f : Processor n Tx → Processor n Tx) :
    (s.update i f).procs i = f (s.procs i) := by
  simp [update]

theorem update_procs_ne (s : State n Tx) {i k : Fin n} (hk : k ≠ i)
    (f : Processor n Tx → Processor n Tx) : (s.update i f).procs k = s.procs k := by
  simp [update, Function.update_of_ne hk]

@[simp] theorem update_pool (s : State n Tx) (i : Fin n) (f : Processor n Tx → Processor n Tx) :
    (s.update i f).pool = s.pool := rfl
@[simp] theorem update_byz (s : State n Tx) (i : Fin n) (f : Processor n Tx → Processor n Tx) :
    (s.update i f).byz = s.byz := rfl
@[simp] theorem update_now (s : State n Tx) (i : Fin n) (f : Processor n Tx → Processor n Tx) :
    (s.update i f).now = s.now := rfl

variable [DecidableEq Tx]

@[simp] theorem transmit_procs (s : State n Tx) (x : Packet n Tx) :
    (s.transmit x).procs = s.procs := rfl
@[simp] theorem transmit_now (s : State n Tx) (x : Packet n Tx) : (s.transmit x).now = s.now := rfl

/-! ### execute の射影 -/

theorem execute_procs_self (s : State n Tx) (i : Fin n) (a : Action n Tx) :
    (s.execute i a).procs i = (s.procs i).execute i a := by
  cases a with
  | send m j =>
    simp only [execute, send, Processor.execute]
    split_ifs <;> simp
  | progress => simp [execute, progress, Processor.execute]

theorem execute_procs_ne (s : State n Tx) {i k : Fin n} (hk : k ≠ i) (a : Action n Tx) :
    (s.execute i a).procs k = s.procs k := by
  cases a with
  | send m j =>
    simp only [execute, send]
    split_ifs <;> simp [update_procs_ne _ hk]
  | progress => simp [execute, progress, update_procs_ne _ hk]

theorem execute_now (s : State n Tx) (i : Fin n) (a : Action n Tx) :
    (s.execute i a).now = s.now := by
  cases a with
  | send m j => simp only [execute, send]; split_ifs <;> simp
  | progress => rfl

/-- i の動作列を大域状態で畳み込んだ後の p_i の局所状態は、局所状態で畳み込んだもの。 -/
theorem foldl_execute_procs_self (s : State n Tx) (i : Fin n) (acts : List (Action n Tx)) :
    (acts.foldl (fun s a => s.execute i a) s).procs i = (s.procs i).executeAll i acts := by
  induction acts generalizing s with
  | nil => rfl
  | cons a acts ih => simp [ih, execute_procs_self]

theorem foldl_execute_procs_ne (s : State n Tx) {i k : Fin n} (hk : k ≠ i)
    (acts : List (Action n Tx)) :
    (acts.foldl (fun s a => s.execute i a) s).procs k = s.procs k := by
  induction acts generalizing s with
  | nil => rfl
  | cons a acts ih => simp [ih, execute_procs_ne _ hk]

/-- 全プロセッサの動作を畳み込む、`step` の最初の段 -/
def act (s : State n Tx) (instr : Instr n Tx) : State n Tx :=
  (List.finRange n).foldl (fun s i => (instr.actions i).foldl (fun s a => s.execute i a) s) s

theorem foldl_act_procs (s : State n Tx) (instr : Instr n Tx) (l : List (Fin n)) (hl : l.Nodup)
    (i : Fin n) :
    ((l.foldl (fun s i => (instr.actions i).foldl (fun s a => s.execute i a) s) s).procs i)
      = if i ∈ l then (s.procs i).executeAll i (instr.actions i) else s.procs i := by
  induction l generalizing s with
  | nil => simp
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hk, hl⟩ := hl
    simp only [List.foldl_cons, ih _ hl, List.mem_cons]
    by_cases hik : i = k
    · subst hik
      simp [hk, foldl_execute_procs_self]
    · simp only [hik, false_or]
      rw [foldl_execute_procs_ne _ hik]

theorem act_procs (s : State n Tx) (instr : Instr n Tx) (i : Fin n) :
    (s.act instr).procs i = (s.procs i).executeAll i (instr.actions i) := by
  simp [act, foldl_act_procs s instr _ (List.nodup_finRange n), List.mem_finRange]

/-! ### 配送・取引・腐敗は局所状態の S 以外を変えない -/

theorem deliver_sgrows (s : State n Tx) (x : Packet n Tx) (i : Fin n) :
    (s.procs i).SGrows ((s.deliver x).procs i) := by
  simp only [deliver]; split_ifs
  · by_cases h : i = x.dst
    · subst h; simp only [update_procs_self]; exact Processor.SGrows.receive _ _
    · rw [update_procs_ne _ h]; exact Processor.SGrows.refl _
  · exact Processor.SGrows.refl _

theorem submit_sgrows (s : State n Tx) (j : Fin n) (tr : Tx) (i : Fin n) :
    (s.procs i).SGrows ((s.submit j tr).procs i) := by
  by_cases h : i = j
  · subst h; simp only [submit, update_procs_self]; exact Processor.SGrows.receive _ _
  · simp only [submit]; rw [update_procs_ne _ h]; exact Processor.SGrows.refl _

theorem foldl_deliver_sgrows (s : State n Tx) (xs : List (Packet n Tx)) (i : Fin n) :
    (s.procs i).SGrows ((xs.foldl deliver s).procs i) := by
  induction xs generalizing s with
  | nil => exact Processor.SGrows.refl _
  | cons x xs ih => exact (deliver_sgrows s x i).trans (ih _)

theorem foldl_submit_sgrows (s : State n Tx) (l : List (Fin n × Tx)) (i : Fin n) :
    (s.procs i).SGrows ((l.foldl (fun s x => s.submit x.1 x.2) s).procs i) := by
  induction l generalizing s with
  | nil => exact Processor.SGrows.refl _
  | cons x l ih => exact (submit_sgrows s x.1 x.2 i).trans (ih _)

omit [DecidableEq Tx] in
theorem foldl_corrupt_procs (s : State n Tx) (l : List (Fin n)) :
    (l.foldl corrupt s).procs = s.procs := by
  induction l generalizing s with
  | nil => rfl
  | cons k l ih => rw [List.foldl_cons, ih, corrupt_procs]

/-! ### pool に packet が入る条件 -/

theorem execute_pool_subset (s : State n Tx) (i : Fin n) (a : Action n Tx) :
    s.pool ⊆ (s.execute i a).pool := by
  cases a with
  | send m j =>
    simp only [execute, send]
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _
  | progress => exact Finset.Subset.refl _

theorem mem_pool_execute {s : State n Tx} {i : Fin n} {a : Action n Tx} {x : Packet n Tx}
    (hx : x ∈ (s.execute i a).pool) :
    x ∈ s.pool ∨ ∃ m j, a = Action.send m j ∧ x = ⟨m, j, s.now⟩
      ∧ (m.signer = some i ∨ m ∈ (s.procs i).S) := by
  cases a with
  | send m j =>
    simp only [execute, send] at hx
    split_ifs at hx with hg
    · simp only [transmit, update_pool] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr ⟨m, j, rfl, rfl, hg⟩
      · exact Or.inl hx
    · exact Or.inl hx
  | progress => exact Or.inl hx

theorem foldl_execute_now (s : State n Tx) (i : Fin n) (acts : List (Action n Tx)) :
    (acts.foldl (fun s a => s.execute i a) s).now = s.now := by
  induction acts generalizing s with
  | nil => rfl
  | cons a acts ih => rw [List.foldl_cons, ih, execute_now]

theorem mem_pool_foldl_execute {s : State n Tx} {i : Fin n} {acts : List (Action n Tx)}
    {x : Packet n Tx} (hx : x ∈ (acts.foldl (fun s a => s.execute i a) s).pool) :
    x ∈ s.pool ∨ ∃ m j, Action.send m j ∈ acts ∧ x = ⟨m, j, s.now⟩
      ∧ (m.signer = some i ∨ m ∈ ((s.procs i).executeAll i acts).S) := by
  induction acts generalizing s with
  | nil => exact Or.inl hx
  | cons a acts ih =>
    rw [List.foldl_cons] at hx
    rcases ih hx with hx | ⟨m, j, hm, hxe, hg⟩
    · rcases mem_pool_execute hx with hx | ⟨m, j, rfl, hxe, hg⟩
      · exact Or.inl hx
      · refine Or.inr ⟨m, j, List.mem_cons_self .., hxe, hg.imp_right fun hm => ?_⟩
        rw [Processor.executeAll_cons]
        exact Processor.S_subset_executeAll i _ acts (Processor.S_subset_execute i _ _ hm)
    · refine Or.inr ⟨m, j, List.mem_cons_of_mem _ hm, ?_, ?_⟩
      · rw [hxe, execute_now]
      · rw [execute_procs_self] at hg
        rwa [Processor.executeAll_cons]

theorem foldl_act_now (s : State n Tx) (instr : Instr n Tx) (l : List (Fin n)) :
    (l.foldl (fun s i => (instr.actions i).foldl (fun s a => s.execute i a) s) s).now = s.now := by
  induction l generalizing s with
  | nil => rfl
  | cons k l ih => rw [List.foldl_cons, ih, foldl_execute_now]

theorem act_now (s : State n Tx) (instr : Instr n Tx) : (s.act instr).now = s.now :=
  foldl_act_now s instr _

theorem mem_pool_foldl_act {s : State n Tx} {instr : Instr n Tx} {l : List (Fin n)}
    (hl : l.Nodup) {x : Packet n Tx}
    (hx : x ∈ (l.foldl (fun s i => (instr.actions i).foldl (fun s a => s.execute i a) s) s).pool) :
    x ∈ s.pool ∨ ∃ k ∈ l, ∃ m j, Action.send m j ∈ instr.actions k ∧ x = ⟨m, j, s.now⟩
      ∧ (m.signer = some k ∨ m ∈ ((s.procs k).executeAll k (instr.actions k)).S) := by
  induction l generalizing s with
  | nil => exact Or.inl hx
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hk, hl⟩ := hl
    rw [List.foldl_cons] at hx
    rcases ih hl hx with hx | ⟨k', hk', m, j, hm, hxe, hg⟩
    · rcases mem_pool_foldl_execute hx with hx | ⟨m, j, hm, hxe, hg⟩
      · exact Or.inl hx
      · exact Or.inr ⟨k, List.mem_cons_self .., m, j, hm, hxe, hg⟩
    · refine Or.inr ⟨k', List.mem_cons_of_mem _ hk', m, j, hm, ?_, ?_⟩
      · rw [hxe, foldl_execute_now]
      · have hne : k' ≠ k := fun h => hk (h ▸ hk')
        rwa [foldl_execute_procs_ne _ hne] at hg

theorem mem_pool_act {s : State n Tx} {instr : Instr n Tx} {x : Packet n Tx}
    (hx : x ∈ (s.act instr).pool) :
    x ∈ s.pool ∨ ∃ k m j, Action.send m j ∈ instr.actions k ∧ x = ⟨m, j, s.now⟩
      ∧ (m.signer = some k ∨ m ∈ ((s.act instr).procs k).S) := by
  rcases mem_pool_foldl_act (List.nodup_finRange n) hx with hx | ⟨k, _, m, j, hm, hxe, hg⟩
  · exact Or.inl hx
  · exact Or.inr ⟨k, m, j, hm, hxe, by rwa [act_procs]⟩

/-! ### 配送・取引・腐敗と pool -/

@[simp] theorem deliver_pool (s : State n Tx) (x : Packet n Tx) : (s.deliver x).pool = s.pool := by
  simp only [deliver]; split_ifs <;> rfl

@[simp] theorem submit_pool (s : State n Tx) (j : Fin n) (tr : Tx) :
    (s.submit j tr).pool = s.pool := rfl

omit [DecidableEq Tx] in
@[simp] theorem corrupt_pool (s : State n Tx) (k : Fin n) : (s.corrupt k).pool = s.pool := rfl

omit [DecidableEq Tx] in
@[simp] theorem tick_pool (s : State n Tx) : s.tick.pool = s.pool := rfl

theorem foldl_deliver_pool (s : State n Tx) (xs : List (Packet n Tx)) :
    (xs.foldl deliver s).pool = s.pool := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, deliver_pool]

theorem foldl_submit_pool (s : State n Tx) (l : List (Fin n × Tx)) :
    (l.foldl (fun s x => s.submit x.1 x.2) s).pool = s.pool := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, ih, submit_pool]

omit [DecidableEq Tx] in
theorem foldl_corrupt_pool (s : State n Tx) (l : List (Fin n)) :
    (l.foldl corrupt s).pool = s.pool := by
  induction l generalizing s with
  | nil => rfl
  | cons k l ih => rw [List.foldl_cons, ih, corrupt_pool]

/-- message が配送で S に入るなら、pool の packet として届いた。 -/
theorem mem_S_deliver {s : State n Tx} {x : Packet n Tx} {k : Fin n} {m : Msg n Tx}
    (hm : m ∈ ((s.deliver x).procs k).S) :
    m ∈ (s.procs k).S ∨ (x ∈ s.pool ∧ x.dst = k ∧ m = x.msg) := by
  simp only [deliver] at hm
  split_ifs at hm with hx
  · by_cases hk : k = x.dst
    · subst hk
      simp only [update_procs_self, Processor.receive_S] at hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact Or.inr ⟨hx, rfl, rfl⟩
      · exact Or.inl hm
    · rw [update_procs_ne _ hk] at hm; exact Or.inl hm
  · exact Or.inl hm

theorem mem_S_foldl_deliver {s : State n Tx} {xs : List (Packet n Tx)} {k : Fin n} {m : Msg n Tx}
    (hm : m ∈ ((xs.foldl deliver s).procs k).S) :
    m ∈ (s.procs k).S ∨ ∃ x ∈ xs, x ∈ s.pool ∧ x.dst = k ∧ m = x.msg := by
  induction xs generalizing s with
  | nil => exact Or.inl hm
  | cons x xs ih =>
    rw [List.foldl_cons] at hm
    rcases ih hm with hm | ⟨y, hy, hyp, hyd, hym⟩
    · rcases mem_S_deliver hm with hm | h
      · exact Or.inl hm
      · exact Or.inr ⟨x, List.mem_cons_self .., h⟩
    · rw [deliver_pool] at hyp
      exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hyp, hyd, hym⟩

theorem mem_S_submit {s : State n Tx} {j : Fin n} {tr : Tx} {k : Fin n} {m : Msg n Tx}
    (hm : m ∈ ((s.submit j tr).procs k).S) : m ∈ (s.procs k).S ∨ m = Msg.tx tr := by
  by_cases hk : k = j
  · subst hk
    simp only [submit, update_procs_self, Processor.receive_S] at hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact Or.inr rfl
    · exact Or.inl hm
  · simp only [submit] at hm; rw [update_procs_ne _ hk] at hm; exact Or.inl hm

theorem mem_S_foldl_submit {s : State n Tx} {l : List (Fin n × Tx)} {k : Fin n} {m : Msg n Tx}
    (hm : m ∈ ((l.foldl (fun s x => s.submit x.1 x.2) s).procs k).S) :
    m ∈ (s.procs k).S ∨ ∃ tr, m = Msg.tx tr := by
  induction l generalizing s with
  | nil => exact Or.inl hm
  | cons x l ih =>
    rw [List.foldl_cons] at hm
    rcases ih hm with hm | h
    · rcases mem_S_submit hm with hm | rfl
      · exact Or.inl hm
      · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr h

/-! ### byz は腐敗でしか変わらず、増えるだけ -/

theorem execute_byz (s : State n Tx) (i : Fin n) (a : Action n Tx) :
    (s.execute i a).byz = s.byz := by
  cases a with
  | send m j => simp only [execute, send]; split_ifs <;> rfl
  | progress => rfl

theorem foldl_execute_byz (s : State n Tx) (i : Fin n) (acts : List (Action n Tx)) :
    (acts.foldl (fun s a => s.execute i a) s).byz = s.byz := by
  induction acts generalizing s with
  | nil => rfl
  | cons a acts ih => rw [List.foldl_cons, ih, execute_byz]

theorem act_byz (s : State n Tx) (instr : Instr n Tx) : (s.act instr).byz = s.byz := by
  unfold act
  induction List.finRange n generalizing s with
  | nil => rfl
  | cons k l ih => rw [List.foldl_cons, ih, foldl_execute_byz]

@[simp] theorem deliver_byz (s : State n Tx) (x : Packet n Tx) : (s.deliver x).byz = s.byz := by
  simp only [deliver]; split_ifs <;> rfl

@[simp] theorem submit_byz (s : State n Tx) (j : Fin n) (tr : Tx) :
    (s.submit j tr).byz = s.byz := rfl

omit [DecidableEq Tx] in
@[simp] theorem tick_byz (s : State n Tx) : s.tick.byz = s.byz := rfl

theorem foldl_deliver_byz (s : State n Tx) (xs : List (Packet n Tx)) :
    (xs.foldl deliver s).byz = s.byz := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, deliver_byz]

theorem foldl_submit_byz (s : State n Tx) (l : List (Fin n × Tx)) :
    (l.foldl (fun s x => s.submit x.1 x.2) s).byz = s.byz := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, ih, submit_byz]

omit [DecidableEq Tx] in
theorem byz_subset_foldl_corrupt (s : State n Tx) (l : List (Fin n)) :
    s.byz ⊆ (l.foldl corrupt s).byz := by
  induction l generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons k l ih =>
    rw [List.foldl_cons]
    refine Finset.Subset.trans ?_ (ih (s.corrupt k))
    exact Finset.subset_insert _ _

/-! ### step の射影 -/

omit [DecidableEq Tx] in
theorem tick_procs (s : State n Tx) (i : Fin n) : s.tick.procs i = (s.procs i).tick := rfl

/-- `step` を段ごとに書いたもの -/
theorem step_eq (s : State n Tx) (instr : Instr n Tx) :
    s.step instr = instr.corrupts.foldl corrupt
      (instr.submits.foldl (fun s x => s.submit x.1 x.2)
        (instr.deliveries.foldl deliver (s.act instr).tick)) := rfl

/-- 1 スロット後の p_i の局所状態は、i の動作を畳み込んで tick したものから、S だけが
    増えたもの。 -/
theorem step_procs (s : State n Tx) (instr : Instr n Tx) (i : Fin n) :
    ((s.procs i).executeAll i (instr.actions i)).tick.SGrows ((s.step instr).procs i) := by
  rw [step_eq, foldl_corrupt_procs]
  have h₁ := foldl_deliver_sgrows (s.act instr).tick instr.deliveries i
  have h₂ := foldl_submit_sgrows (instr.deliveries.foldl deliver (s.act instr).tick)
    instr.submits i
  rw [tick_procs, act_procs] at h₁
  exact h₁.trans h₂

theorem step_pool (s : State n Tx) (instr : Instr n Tx) :
    (s.step instr).pool = (s.act instr).pool := by
  rw [step_eq, foldl_corrupt_pool, foldl_submit_pool, foldl_deliver_pool, tick_pool]

@[simp] theorem deliver_now (s : State n Tx) (x : Packet n Tx) : (s.deliver x).now = s.now := by
  simp only [deliver]; split_ifs <;> rfl

@[simp] theorem submit_now (s : State n Tx) (j : Fin n) (tr : Tx) :
    (s.submit j tr).now = s.now := rfl

omit [DecidableEq Tx] in
@[simp] theorem corrupt_now (s : State n Tx) (k : Fin n) : (s.corrupt k).now = s.now := rfl

omit [DecidableEq Tx] in
@[simp] theorem tick_now (s : State n Tx) : s.tick.now = ⟨s.now.val + 1⟩ := rfl

theorem foldl_deliver_now (s : State n Tx) (xs : List (Packet n Tx)) :
    (xs.foldl deliver s).now = s.now := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, deliver_now]

theorem foldl_submit_now (s : State n Tx) (l : List (Fin n × Tx)) :
    (l.foldl (fun s x => s.submit x.1 x.2) s).now = s.now := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, ih, submit_now]

omit [DecidableEq Tx] in
theorem foldl_corrupt_now (s : State n Tx) (l : List (Fin n)) :
    (l.foldl corrupt s).now = s.now := by
  induction l generalizing s with
  | nil => rfl
  | cons k l ih => rw [List.foldl_cons, ih, corrupt_now]

theorem step_now (s : State n Tx) (instr : Instr n Tx) : (s.step instr).now = ⟨s.now.val + 1⟩ := by
  rw [step_eq, foldl_corrupt_now, foldl_submit_now, foldl_deliver_now, tick_now, act_now]

/-- 1 スロット後に p_k の S にある message は、動作の後からあったか、pool の packet として
    届いたか、取引の message。 -/
theorem mem_S_step {s : State n Tx} {instr : Instr n Tx} {k : Fin n} {m : Msg n Tx}
    (hm : m ∈ ((s.step instr).procs k).S) :
    m ∈ ((s.act instr).procs k).S
      ∨ (∃ x ∈ instr.deliveries, x ∈ (s.act instr).pool ∧ x.dst = k ∧ m = x.msg)
      ∨ ∃ tr, m = Msg.tx tr := by
  rw [step_eq, foldl_corrupt_procs] at hm
  rcases mem_S_foldl_submit hm with hm | h
  · rcases mem_S_foldl_deliver hm with hm | ⟨x, hx, hxp, hxd, hxm⟩
    · rw [tick_procs, Processor.tick_S] at hm; exact Or.inl hm
    · rw [tick_pool] at hxp; exact Or.inr (Or.inl ⟨x, hx, hxp, hxd, hxm⟩)
  · exact Or.inr (Or.inr h)

theorem byz_subset_step (s : State n Tx) (instr : Instr n Tx) : s.byz ⊆ (s.step instr).byz := by
  rw [step_eq]
  have h : (instr.submits.foldl (fun s x => s.submit x.1 x.2)
      (instr.deliveries.foldl deliver (s.act instr).tick)).byz = s.byz := by
    rw [foldl_submit_byz, foldl_deliver_byz, tick_byz, act_byz]
  rw [← h]
  exact byz_subset_foldl_corrupt _ _

/-- S は 1 スロットで減らない。 -/
theorem S_subset_step (s : State n Tx) (instr : Instr n Tx) (k : Fin n) :
    (s.procs k).S ⊆ ((s.step instr).procs k).S :=
  (Processor.S_subset_executeAll k _ _).trans (step_procs s instr k).S

end State

end Minimmit
