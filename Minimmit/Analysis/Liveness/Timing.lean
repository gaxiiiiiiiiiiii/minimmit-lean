import Minimmit.Model.Constraint.Run

/-!
# 時間についての補題

view は減らない、timer は現在の view に入ってからのスロット数、正直者が送った message は
部分同期の期限までに全員の S に入る、新しい証明書は転送されて全員に届く、証明書を持つ
正直者は次のスロットで view を進める。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {GST : Time} {lead : View → Fin n} {s₀ : State n Tx}
  {instrs : Nat → Instr n Tx}

/-- スロット t の冒頭の p_i の view -/
def viewAt (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (i : Fin n) (t : Nat) : View :=
  ((State.run s₀ instrs t).procs i).view

/-- スロット t の冒頭の p_i の timer -/
def timerAt (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (i : Fin n) (t : Nat) : Nat :=
  ((State.run s₀ instrs t).procs i).timer

theorem run_succ (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (t : Nat) :
    State.run s₀ instrs (t + 1) = (State.run s₀ instrs t).step (instrs t) := rfl

/-! ### view は減らない -/

theorem Processor.view_le_execute (i : Fin n) (p : Processor n Tx) (a : Action n Tx) :
    p.view.val ≤ (p.execute i a).view.val := by
  cases a with
  | send m j =>
    simp only [Processor.execute]
    split_ifs
    · rw [Processor.send_view]
    · exact le_refl _
  | progress => simp [Processor.execute, Processor.progress]

theorem Processor.view_le_executeAll (i : Fin n) (p : Processor n Tx) (acts : List (Action n Tx)) :
    p.view.val ≤ (p.executeAll i acts).view.val := by
  induction acts generalizing p with
  | nil => exact le_refl _
  | cons a acts ih => exact (Processor.view_le_execute i p a).trans (ih _)

theorem viewAt_le_succ (i : Fin n) (t : Nat) :
    (viewAt s₀ instrs i t).val ≤ (viewAt s₀ instrs i (t + 1)).val := by
  unfold viewAt
  rw [run_succ, (State.step_procs _ _ i).view, Processor.tick_view]
  exact Processor.view_le_executeAll i _ _

theorem viewAt_mono (i : Fin n) {t t' : Nat} (h : t ≤ t') :
    (viewAt s₀ instrs i t).val ≤ (viewAt s₀ instrs i t').val := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (viewAt_le_succ i _)

/-! ### timer -/

theorem Processor.executeAll_timer (i : Fin n) (p : Processor n Tx) (acts : List (Action n Tx)) :
    ((p.executeAll i acts).timer = 0 ∧ p.view.val < (p.executeAll i acts).view.val)
      ∨ ((p.executeAll i acts).timer = p.timer ∧ (p.executeAll i acts).view = p.view) := by
  induction acts generalizing p with
  | nil => exact Or.inr ⟨rfl, rfl⟩
  | cons a acts ih =>
    rw [Processor.executeAll_cons]
    rcases ih (p.execute i a) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, lt_of_le_of_lt (Processor.view_le_execute i p a) h2⟩
    · cases a with
      | send m j =>
        simp only [Processor.execute] at h1 h2 ⊢
        split_ifs at h1 h2 ⊢
        · exact Or.inr
            ⟨h1.trans (Processor.send_timer i p m j), h2.trans (Processor.send_view i p m j)⟩
        · exact Or.inr ⟨h1, h2⟩
      | progress =>
        left
        refine ⟨h1, ?_⟩
        rw [h2]
        simp [Processor.execute, Processor.progress]

theorem timerAt_succ (i : Fin n) (t : Nat) :
    (timerAt s₀ instrs i (t + 1) = 1 ∧ (viewAt s₀ instrs i t).val
    < (viewAt s₀ instrs i (t + 1)).val)
      ∨ (timerAt s₀ instrs i (t + 1) = timerAt s₀ instrs i t + 1
          ∧ viewAt s₀ instrs i (t + 1) = viewAt s₀ instrs i t) := by
  unfold timerAt viewAt
  rw [run_succ, (State.step_procs _ _ i).timer, (State.step_procs _ _ i).view, Processor.tick_timer,
    Processor.tick_view]
  rcases Processor.executeAll_timer i ((State.run s₀ instrs t).procs i) ((instrs t).actions i)
    with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], h2⟩
  · exact Or.inr ⟨by rw [h1], h2⟩

/-- 同じ view にとどまる間、timer は 1 ずつ増える。 -/
theorem timerAt_add (i : Fin n) (t k : Nat)
    (h : ∀ k' ≤ k, viewAt s₀ instrs i (t + k') = viewAt s₀ instrs i t) :
    timerAt s₀ instrs i (t + k) = timerAt s₀ instrs i t + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := ih fun k' hk' => h k' (Nat.le_succ_of_le hk')
    rcases timerAt_succ (s₀ := s₀) (instrs := instrs) i (t + k) with ⟨_, h2⟩ | ⟨h1, _⟩
    · exfalso
      have := h (k + 1) (le_refl _)
      rw [← Nat.add_assoc] at this
      rw [this, h k (Nat.le_succ k)] at h2
      exact lt_irrefl _ h2
    · rw [← Nat.add_assoc, h1, hk]; omega

/-! ### now と pool -/

theorem run_now (hinit : Init s₀) (t : Nat) : (State.run s₀ instrs t).now = ⟨t⟩ := by
  induction t with
  | zero => exact hinit.now
  | succ t ih => rw [State.run, State.step_now, ih]

theorem State.pool_subset_foldl_execute (s : State n Tx) (i : Fin n) (acts : List (Action n Tx)) :
    s.pool ⊆ (acts.foldl (fun s a => s.execute i a) s).pool := by
  induction acts generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons a acts ih => exact (State.execute_pool_subset s i a).trans (ih _)

theorem State.pool_subset_foldl_act (s : State n Tx) (instr : Instr n Tx) (l : List (Fin n)) :
    s.pool ⊆
      (l.foldl (fun s i => (instr.actions i).foldl (fun s a => s.execute i a) s) s).pool := by
  induction l generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons k l ih => exact (State.pool_subset_foldl_execute s k _).trans (ih _)

theorem State.pool_subset_step (s : State n Tx) (instr : Instr n Tx) :
    s.pool ⊆ (s.step instr).pool := by
  rw [State.step_pool]; exact State.pool_subset_foldl_act s instr _

theorem pool_subset_run {t t' : Nat} (h : t ≤ t') :
    (State.run s₀ instrs t).pool ⊆ (State.run s₀ instrs t').pool := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (State.pool_subset_step _ _)

/-- 遅延の上界を緩めても部分同期は成り立つ。 -/
theorem PartialSync.mono {δ Δ : Nat} (hs : PartialSync δ GST s₀ instrs) (hδ : δ ≤ Δ) :
    PartialSync Δ GST s₀ instrs where
  timely := fun t x hx hT => hs.timely t x hx (by omega)
  one_le := le_trans hs.one_le hδ

/-! ### 正直者の送信は届く -/

theorem State.mem_pool_foldl_execute_of_send (s : State n Tx) (i : Fin n)
    {acts : List (Action n Tx)}
    {m : Msg n Tx} {j : Fin n} (h : Action.send m j ∈ acts)
    (hg : Processor.GuardOK i (s.procs i) acts) :
    (⟨m, j, s.now⟩ : Packet n Tx) ∈ (acts.foldl (fun s a => s.execute i a) s).pool := by
  induction acts generalizing s with
  | nil => simp at h
  | cons a acts ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · apply State.pool_subset_foldl_execute
      have hc := hg.1 m j rfl
      simp only [State.execute, State.send, if_pos hc, State.transmit, State.update_pool,
        State.update_now]
      exact Finset.mem_insert_self _ _
    · have := ih (s.execute i a) h (by rw [State.execute_procs_self]; exact hg.2)
      rwa [State.execute_now] at this

theorem State.mem_pool_foldl_act_of_send (s : State n Tx) (instr : Instr n Tx) {l : List (Fin n)}
    (hl : l.Nodup) {i : Fin n} (hi : i ∈ l) {m : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ instr.actions i)
    (hg : Processor.GuardOK i (s.procs i) (instr.actions i)) :
    (⟨m, j, s.now⟩ : Packet n Tx)
      ∈ (l.foldl (fun s i => (instr.actions i).foldl (fun s a => s.execute i a) s) s).pool := by
  induction l generalizing s with
  | nil => simp at hi
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hi
    · exact State.pool_subset_foldl_act _ instr l (State.mem_pool_foldl_execute_of_send s i h hg)
    · have hne : i ≠ k := fun h' => hl.1 (h' ▸ hi)
      have := ih ((instr.actions k).foldl (fun s a => s.execute k a) s) hl.2 hi (by
        rw [State.foldl_execute_procs_ne _ hne]; exact hg)
      rwa [State.foldl_execute_now] at this

theorem State.mem_pool_step_of_send (s : State n Tx) (instr : Instr n Tx) {i : Fin n} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ instr.actions i)
    (hg : Processor.GuardOK i (s.procs i) (instr.actions i)) :
    (⟨m, j, s.now⟩ : Packet n Tx) ∈ (s.step instr).pool := by
  rw [State.step_pool]
  exact State.mem_pool_foldl_act_of_send s instr (List.nodup_finRange n) (List.mem_finRange i) h hg

/-- 正直者 p_i がスロット t に j へ送った message の packet は、t + 1 以降の pool にある。 -/
theorem mem_pool_run_of_send (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {m : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (instrs t).actions i) {t' : Nat} (ht : t + 1 ≤ t') :
    (⟨m, j, ⟨t⟩⟩ : Packet n Tx) ∈ (State.run s₀ instrs t').pool := by
  have hg : Processor.GuardOK i ((State.run s₀ instrs t).procs i) ((instrs t).actions i) := by
    rw [hh t i (hi t)]; exact Algo.guardOK_step f Δ lead i _
  have := State.mem_pool_step_of_send (State.run s₀ instrs t) (instrs t) h hg
  rw [run_now hinit] at this
  exact pool_subset_run ht this

/-- 正直者 p_i がスロット t に j へ送った message は、t + 1 以降で期限 max(GST, t) + δ に
    達したスロットの p_j の S にある。 -/
theorem delivered (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ GST s₀ instrs)
    {i : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {m : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (instrs t).actions i) {T : Nat} (hT₁ : t + 1 ≤ T)
    (hT₂ : max GST.val t + δ ≤ T) : m ∈ ((State.run s₀ instrs T).procs j).S := by
  have hx := mem_pool_run_of_send hinit hh hi h hT₁
  have := hs.timely T ⟨m, j, ⟨t⟩⟩ hx
  rw [run_now hinit] at this
  exact this hT₂

/-! ### 証明書の転送 -/

theorem prevS_run (i : Fin n) (t : Nat) :
    ((State.run s₀ instrs (t + 1)).procs i).prevS
      = (((State.run s₀ instrs t).procs i).executeAll i ((instrs t).actions i)).S := by
  rw [run_succ, (State.step_procs _ _ i).prevS, Processor.tick_prevS]

/-- 正直者の prevS は、前スロットの動作を終えた時点の S。 -/
theorem prevS_run_honest (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    (t : Nat) :
    ((State.run s₀ instrs (t + 1)).procs i).prevS
      = (Algo.st5 f Δ lead i ((State.run s₀ instrs t).procs i)).S := by
  rw [prevS_run, hh t i (hi t), Algo.executeAll_step, Algo.stepPair_S]

theorem prevS_zero (hinit : Init s₀) (i : Fin n) : ((State.run s₀ instrs 0).procs i).prevS = ∅ := by
  rw [State.run, hinit.procs i]; rfl

/-- 正直者が動作を終えた時点の S に nullification を持つなら、それが初めて完成した
    スロット t' ≤ t に、番号の小さい順 2f + 1 人の nullify を全員へ送っている。 -/
theorem forward_nullification_end (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {v : View}
    (ht : Nullified f (Algo.st5 f Δ lead i ((State.run s₀ instrs t).procs i)).S v) :
    ∃ t' ≤ t, Nullified f (Algo.st5 f Δ lead i ((State.run s₀ instrs t').procs i)).S v
      ∧ ∀ q ∈ Algo.leastNullifiers f (Algo.st5 f Δ lead i ((State.run s₀ instrs t').procs i)).S v,
        ∀ j,
        Action.send (Msg.nullify q v) j ∈ (instrs t').actions i := by
  classical
  have hex :
      ∃ t', Nullified f (Algo.st5 f Δ lead i ((State.run s₀ instrs t').procs i)).S v := ⟨t, ht⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ht, Nat.find_spec hex, fun q hq j => ?_⟩
  have hnew : ¬ Nullified f (Algo.st5 f Δ lead i
      ((State.run s₀ instrs (Nat.find hex)).procs i)).prevS v := by
    rw [Algo.st5_prevS]
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, prevS_zero hinit]
      simp [Nullified, nullifiers]
    · obtain ⟨t'', ht''⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      rw [ht'', prevS_run_honest hh hi]
      exact Nat.find_min hex (by rw [ht'']; exact Nat.lt_succ_self t'')
  rw [hh (Nat.find hex) i (hi _)]
  exact Algo.send_mem_step_of_mem_forwardMsgs
    (Algo.mem_forwardMsgs_nullify (Nat.find_spec hex) hnew hq) j

/-- 正直者が nullification を持つなら、その動作を終えた時点の S で初めてそれが完成した
    スロット t' ≤ t に、番号の小さい順 2f + 1 人の nullify を全員へ送っている。 -/
theorem forward_nullification (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {v : View}
    (h : Nullified f ((State.run s₀ instrs t).procs i).S v) :
    ∃ t' ≤ t, Nullified f (Algo.st5 f Δ lead i ((State.run s₀ instrs t').procs i)).S v
      ∧ ∀ q ∈ Algo.leastNullifiers f (Algo.st5 f Δ lead i ((State.run s₀ instrs t').procs i)).S v,
        ∀ j,
        Action.send (Msg.nullify q v) j ∈ (instrs t').actions i :=
  forward_nullification_end hinit hh hi (h.mono (Algo.S_subset_st5 f Δ lead i _))

theorem forward_mnotarisation_end (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {b : Block n Tx} (hg : b ≠ .gen)
    (ht : MNotarised f (Algo.st5 f Δ lead i ((State.run s₀ instrs t).procs i)).S b) :
    ∃ t' ≤ t, MNotarised f (Algo.st5 f Δ lead i ((State.run s₀ instrs t').procs i)).S b
      ∧ ∀ q ∈ Algo.leastVoters f (Algo.st5 f Δ lead i ((State.run s₀ instrs t').procs i)).S b,
        ∀ j,
        Action.send (Msg.vote q b) j ∈ (instrs t').actions i := by
  classical
  have hex :
      ∃ t', MNotarised f (Algo.st5 f Δ lead i ((State.run s₀ instrs t').procs i)).S b := ⟨t, ht⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ht, Nat.find_spec hex, fun q hq j => ?_⟩
  have hnew : ¬ MNotarised f (Algo.st5 f Δ lead i
      ((State.run s₀ instrs (Nat.find hex)).procs i)).prevS b := by
    rw [Algo.st5_prevS]
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, prevS_zero hinit]
      intro hM
      rcases hM with hM | hM
      · exact hg hM
      · simp [voters] at hM
    · obtain ⟨t'', ht''⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      rw [ht'', prevS_run_honest hh hi]
      exact Nat.find_min hex (by rw [ht'']; exact Nat.lt_succ_self t'')
  rw [hh (Nat.find hex) i (hi _)]
  exact Algo.send_mem_step_of_mem_forwardMsgs
    (Algo.mem_forwardMsgs_vote (Nat.find_spec hex) hnew hq) j

/-- 正直者が genesis でないブロックの M-notarisation を持つなら、その動作を終えた時点の S で
    初めてそれが完成したスロットに、番号の小さい順 2f + 1 人の票を全員へ送っている。 -/
theorem forward_mnotarisation (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {b : Block n Tx} (hg : b ≠ .gen)
    (h : MNotarised f ((State.run s₀ instrs t).procs i).S b) :
    ∃ t' ≤ t, MNotarised f (Algo.st5 f Δ lead i ((State.run s₀ instrs t').procs i)).S b
      ∧ ∀ q ∈ Algo.leastVoters f (Algo.st5 f Δ lead i ((State.run s₀ instrs t').procs i)).S b,
        ∀ j,
        Action.send (Msg.vote q b) j ∈ (instrs t').actions i :=
  forward_mnotarisation_end hinit hh hi hg (h.mono (Algo.S_subset_st5 f Δ lead i _))

/-- 正直者 p_i がスロット t に nullification を持つなら、p_j は期限までにそれを持つ。 -/
theorem nullified_all (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ GST s₀ instrs)
    {i j : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {v : View}
    (h : Nullified f ((State.run s₀ instrs t).procs i).S v) {T : Nat} (hT₁ : t + 1 ≤ T)
    (hT₂ : max GST.val t + δ ≤ T) : Nullified f ((State.run s₀ instrs T).procs j).S v := by
  obtain ⟨t', ht', hn', hsend⟩ := forward_nullification hinit hh hi h
  refine (Algo.card_leastNullifiers hn').symm.le.trans (Finset.card_le_card fun q hq => ?_)
  rw [mem_nullifiers]
  exact delivered hinit hh hs hi (hsend q hq j) (by omega)
    ((Nat.add_le_add_right (max_le_max (le_refl _) ht') δ).trans hT₂)

theorem mnotarised_all (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ GST s₀ instrs)
    {i j : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {b : Block n Tx}
    (h : MNotarised f ((State.run s₀ instrs t).procs i).S b) {T : Nat} (hT₁ : t + 1 ≤ T)
    (hT₂ : max GST.val t + δ ≤ T) : MNotarised f ((State.run s₀ instrs T).procs j).S b := by
  by_cases hg : b = .gen
  · exact Or.inl hg
  obtain ⟨t', ht', hn', hsend⟩ := forward_mnotarisation hinit hh hi hg h
  rcases hn' with h' | hn'
  · exact Or.inl h'
  right
  refine (Algo.card_leastVoters hn').symm.le.trans (Finset.card_le_card fun q hq => ?_)
  rw [mem_voters]
  exact delivered hinit hh hs hi (hsend q hq j) (by omega)
    ((Nat.add_le_add_right (max_le_max (le_refl _) ht') δ).trans hT₂)

/-- `nullified_all` の、動作を終えた時点の S についての版 -/
theorem nullified_all_end (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ GST s₀ instrs) {i j : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {v : View}
    (h : Nullified f (Algo.st5 f Δ lead i ((State.run s₀ instrs t).procs i)).S v) {T : Nat}
    (hT₁ : t + 1 ≤ T) (hT₂ : max GST.val t + δ ≤ T) :
    Nullified f ((State.run s₀ instrs T).procs j).S v := by
  obtain ⟨t', ht', hn', hsend⟩ := forward_nullification_end hinit hh hi h
  refine (Algo.card_leastNullifiers hn').symm.le.trans (Finset.card_le_card fun q hq => ?_)
  rw [mem_nullifiers]
  exact delivered hinit hh hs hi (hsend q hq j) (by omega)
    ((Nat.add_le_add_right (max_le_max (le_refl _) ht') δ).trans hT₂)

theorem mnotarised_all_end (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ GST s₀ instrs) {i j : Fin n} (hi : Correct s₀ instrs i) {t : Nat}
    {b : Block n Tx}
    (h : MNotarised f (Algo.st5 f Δ lead i ((State.run s₀ instrs t).procs i)).S b) {T : Nat}
    (hT₁ : t + 1 ≤ T) (hT₂ : max GST.val t + δ ≤ T) :
    MNotarised f ((State.run s₀ instrs T).procs j).S b := by
  by_cases hg : b = .gen
  · exact Or.inl hg
  obtain ⟨t', ht', hn', hsend⟩ := forward_mnotarisation_end hinit hh hi hg h
  rcases hn' with h' | hn'
  · exact Or.inl h'
  right
  refine (Algo.card_leastVoters hn').symm.le.trans (Finset.card_le_card fun q hq => ?_)
  rw [mem_voters]
  exact delivered hinit hh hs hi (hsend q hq j) (by omega)
    ((Nat.add_le_add_right (max_le_max (le_refl _) ht') δ).trans hT₂)

/-! ### timer と view の滞在 -/

theorem timerAt_le_slot (hinit : Init s₀) (i : Fin n) (t : Nat) : timerAt s₀ instrs i t ≤ t := by
  induction t with
  | zero =>
    show ((State.run s₀ instrs 0).procs i).timer ≤ 0
    rw [State.run, hinit.procs i]; exact le_refl _
  | succ t ih =>
    rcases timerAt_succ (s₀ := s₀) (instrs := instrs) i t with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; omega
    · rw [h1]; omega

/-- timer が m より大きければ、m スロット前から同じ view にいる。 -/
theorem viewAt_eq_of_lt_timer (hinit : Init s₀) (i : Fin n) (t : Nat) :
    ∀ m, m < timerAt s₀ instrs i t →
      ∀ m' ≤ m, viewAt s₀ instrs i (t - m') = viewAt s₀ instrs i t := by
  intro m
  induction m with
  | zero => intro _ m' hm'; rw [Nat.le_zero.mp hm', Nat.sub_zero]
  | succ m ih =>
    intro hm m' hm'
    rcases Nat.le_succ_iff.mp hm' with hle | rfl
    · exact ih (Nat.lt_of_succ_lt hm) m' hle
    · have hle := timerAt_le_slot (instrs := instrs) hinit i t
      have hstay : ∀ k' ≤ m, viewAt s₀ instrs i (t - m + k') = viewAt s₀ instrs i (t - m) := by
        intro k' hk'
        have e1 := ih (Nat.lt_of_succ_lt hm) (m - k') (Nat.sub_le _ _)
        have e2 := ih (Nat.lt_of_succ_lt hm) m (le_refl _)
        rw [show t - m + k' = t - (m - k') by omega, e1, e2]
      have htimer := timerAt_add (s₀ := s₀) (instrs := instrs) i (t - m) m hstay
      rw [show t - m + m = t by omega] at htimer
      rcases timerAt_succ (s₀ := s₀) (instrs := instrs) i (t - (m + 1)) with ⟨h1, _⟩ | ⟨_, h2⟩
      · exfalso
        rw [show t - (m + 1) + 1 = t - m by omega] at h1
        omega
      · rw [show t - (m + 1) + 1 = t - m by omega] at h2
        rw [← h2]
        exact ih (Nat.lt_of_succ_lt hm) m (le_refl _)

/-! ### 正直者の反応 -/

/-- 次のスロットの冒頭の view は、16〜21 行を評価した後の view。 -/
theorem viewAt_succ_eq (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    (t : Nat) :
    viewAt s₀ instrs i (t + 1) = (Algo.st1 f i ((State.run s₀ instrs t).procs i)).view := by
  unfold viewAt
  rw [run_succ, (State.step_procs _ _ i).view, Processor.tick_view, hh t i (hi t),
    Algo.executeAll_step, Algo.stepPair_view]

theorem S_stepPair_subset_succ (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) (t : Nat) :
    (Algo.stepPair f Δ lead i ((State.run s₀ instrs t).procs i)).1.S
      ⊆ ((State.run s₀ instrs (t + 1)).procs i).S := by
  intro m hm
  rw [← Algo.executeAll_step, ← hh t i (hi t)] at hm
  have h2 := (State.step_procs (State.run s₀ instrs t) (instrs t) i).S
  rw [Processor.tick_S] at h2
  rw [run_succ]; exact h2 hm

theorem S_st5_subset_succ (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    (t : Nat) :
    (Algo.st5 f Δ lead i ((State.run s₀ instrs t).procs i)).S
      ⊆ ((State.run s₀ instrs (t + 1)).procs i).S :=
  (Algo.S_st5_subset_stepPair f Δ lead i _).trans (S_stepPair_subset_succ hh hi t)

theorem Algo.hasCert_of_mnotarised {f : Nat} {S : Finset (Msg n Tx)} {b : Block n Tx}
    (hg : b ≠ .gen) (h : MNotarised f S b) : Algo.HasCert f S b.view := by
  right
  rcases h with h' | h'
  · exact absurd h' hg
  · obtain ⟨q, hq⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos _) h')
    exact List.ne_nil_of_mem
      (Algo.mem_mNotarisedAt_of (Algo.mem_votedBlocks (mem_voters.mp hq)) (Or.inr h'))

/-- 現在の view の証明書を持つ正直者は、次のスロットには view を進めている。 -/
theorem leave_of_hasCert (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    {t : Nat} {v : View} (hv : viewAt s₀ instrs i t = v)
    (h : Algo.HasCert f ((State.run s₀ instrs t).procs i).S v) :
    v.val < (viewAt s₀ instrs i (t + 1)).val := by
  rw [viewAt_succ_eq hh hi t]
  have hpv : ((State.run s₀ instrs t).procs i).view = v := hv
  rw [← hpv] at h ⊢
  exact Algo.view_lt_st1_of_hasCert i h

theorem leave_of_nullified (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    {t : Nat} {v : View} (hv : viewAt s₀ instrs i t = v)
    (h : Nullified f ((State.run s₀ instrs t).procs i).S v) :
    v.val < (viewAt s₀ instrs i (t + 1)).val :=
  leave_of_hasCert hh hi hv (Or.inl h)

theorem leave_of_mnotarised (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    {t : Nat} {b : Block n Tx} (hv : viewAt s₀ instrs i t = b.view) (hg : b ≠ .gen)
    (h : MNotarised f ((State.run s₀ instrs t).procs i).S b) :
    b.view.val < (viewAt s₀ instrs i (t + 1)).val :=
  leave_of_hasCert hh hi hv (Algo.hasCert_of_mnotarised hg h)

theorem Algo.view_le_st5 (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.view.val ≤ (Algo.st5 f Δ lead i p).view.val := by
  rw [Algo.st5_view]; exact Algo.view_le_st1 f i p

/-- 正直者が view v を越えて進んだなら、スロット冒頭の S に view v の nullification か
    view v のブロックの M-notarisation がある。 -/
theorem leave_view_cert (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    {t : Nat} {v : View} (h1 : (viewAt s₀ instrs i t).val ≤ v.val)
    (h2 : v.val < (viewAt s₀ instrs i (t + 1)).val) :
    Nullified f ((State.run s₀ instrs t).procs i).S v
      ∨ ∃ b, b.view = v ∧ MNotarised f ((State.run s₀ instrs t).procs i).S b := by
  rw [viewAt_succ_eq hh hi t] at h2
  rcases Algo.st1_certs h1 h2 with h | h
  · exact Or.inl h
  · right
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨b, (Algo.mem_mNotarisedAt hb).1, (Algo.mem_mNotarisedAt hb).2⟩

/-- view を進めなかった正直者の 16〜21 行は何もしない。 -/
theorem st1_eq_of_not_leave (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
    {t : Nat} (h : ¬ (viewAt s₀ instrs i t).val < (viewAt s₀ instrs i (t + 1)).val) :
    Algo.st1 f i ((State.run s₀ instrs t).procs i) = (State.run s₀ instrs t).procs i := by
  apply Algo.st1_eq_of_view
  apply View.val_injective
  rw [viewAt_succ_eq hh hi t] at h
  have := Algo.view_le_st1 f i ((State.run s₀ instrs t).procs i)
  exact le_antisymm (not_lt.mp h) this

/-- timer が 2Δ に達した正直者は、そのスロットの終わりまでに現在の view のブロックに投票して
    いるか、nullify を送っているか、view を進めている。 -/
theorem timeout (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {v : View} (hv : viewAt s₀ instrs i t = v)
    (ht : timerAt s₀ instrs i t = 2 * Δ) :
    (∃ b, b.view = v ∧ Msg.vote i b ∈ ((State.run s₀ instrs (t + 1)).procs i).S)
      ∨ Msg.nullify i v ∈ ((State.run s₀ instrs (t + 1)).procs i).S
      ∨ v.val < (viewAt s₀ instrs i (t + 1)).val := by
  by_cases hlt : v.val < (viewAt s₀ instrs i (t + 1)).val
  · exact Or.inr (Or.inr hlt)
  have hpv : ((State.run s₀ instrs t).procs i).view = v := hv
  have h2 : Algo.st1 f i ((State.run s₀ instrs t).procs i) = (State.run s₀ instrs t).procs i :=
    st1_eq_of_not_leave hh hi (by rw [hv]; exact hlt)
  have hL : Algo.LocalInv f i (Algo.st3 f lead i ((State.run s₀ instrs t).procs i)) :=
    Algo.localInv_st3 (localInv_run hinit hh hi t)
  have h4v : (Algo.st3 f lead i ((State.run s₀ instrs t).procs i)).view = v := by
    rw [Algo.st3_view, h2, hpv]
  have h4t : (Algo.st3 f lead i ((State.run s₀ instrs t).procs i)).timer = 2 * Δ := by
    rw [Algo.st3_timer, h2]; exact ht
  have hsub : (Algo.st3 f lead i ((State.run s₀ instrs t).procs i)).S
      ⊆ ((State.run s₀ instrs (t + 1)).procs i).S :=
    (Algo.S_st3_subset_st5 f Δ lead i _).trans (S_st5_subset_succ hh hi t)
  rcases hnot : (Algo.st3 f lead i ((State.run s₀ instrs t).procs i)).notarised with _ | b
  · cases hnl : (Algo.st3 f lead i ((State.run s₀ instrs t).procs i)).nullified
    · right; left
      have := Algo.nullifyTimeout_fires (i := i) h4t hnl hnot
      rw [h4v] at this
      exact ((Algo.S_st4_subset_st5 f Δ lead i _).trans (S_st5_subset_succ hh hi t)) this
    · right; left
      have := hL.null_mem hnl
      rw [h4v] at this
      exact hsub this
  · left
    exact ⟨b, (hL.notar_view b hnot).trans h4v, hsub (hL.notar_mem b hnot)⟩

/-- 投票済みの正直者が、進捗のなさの証拠を持てば、次のスロットまでに nullify を送るか
    view を進めている。 -/
theorem noprogress_reaction (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {v : View} {b : Block n Tx} (hv : viewAt s₀ instrs i t = v)
    (hb : ((State.run s₀ instrs t).procs i).notarised = some b)
    (h : NoProgress f ((State.run s₀ instrs t).procs i).S v (some b)) :
    Msg.nullify i v ∈ ((State.run s₀ instrs (t + 1)).procs i).S
      ∨ v.val < (viewAt s₀ instrs i (t + 1)).val := by
  by_cases hlt : v.val < (viewAt s₀ instrs i (t + 1)).val
  · exact Or.inr hlt
  left
  have hpv : ((State.run s₀ instrs t).procs i).view = v := hv
  have h2 : Algo.st1 f i ((State.run s₀ instrs t).procs i) = (State.run s₀ instrs t).procs i :=
    st1_eq_of_not_leave hh hi (by rw [hv]; exact hlt)
  have hLp := localInv_run hinit hh hi t
  have hL5 : Algo.LocalInv f i (Algo.st4 f Δ lead i ((State.run s₀ instrs t).procs i)) :=
    Algo.localInv_st4 hLp
  have h5v : (Algo.st4 f Δ lead i ((State.run s₀ instrs t).procs i)).view = v := by
    rw [Algo.st4_view, h2, hpv]
  have hvote : Msg.vote i b ∈ (Algo.st4 f Δ lead i ((State.run s₀ instrs t).procs i)).S :=
    Algo.S_subset_st4 f Δ lead i _ (hLp.notar_mem b hb)
  have hbv : b.view = v := (hLp.notar_view b hb).trans hv
  have hnot5 : (Algo.st4 f Δ lead i ((State.run s₀ instrs t).procs i)).notarised = some b :=
    ((hL5.notar b hvote).2.resolve_left (by rw [hbv, h5v]; exact lt_irrefl _)).2
  have hnp5 : NoProgress f (Algo.st4 f Δ lead i ((State.run s₀ instrs t).procs i)).S
      (Algo.st4 f Δ lead i ((State.run s₀ instrs t).procs i)).view (some b) := by
    rw [h5v]; exact h.mono (Algo.S_subset_st4 f Δ lead i _)
  cases hnl : (Algo.st4 f Δ lead i ((State.run s₀ instrs t).procs i)).nullified
  · have := Algo.nullifyNoProgress_fires (i := i) hnl hnot5 hnp5
    rw [h5v] at this
    exact S_st5_subset_succ hh hi t this
  · have := hL5.null_mem hnl
    rw [h5v] at this
    exact (Algo.S_st4_subset_st5 f Δ lead i _).trans (S_st5_subset_succ hh hi t) this

end Minimmit
