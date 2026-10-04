import Minimmit.Model.Algo.Disseminate

/-!
# Algorithm 1 の各部分の補題

各部分の入力状態 st1〜st5 と動作の列の分解、各部分で返す局所状態が動作の列の畳み込みと一致すること、
各部分の send がその時点の `canSend` を満たすこと、各部分で S が減らないこと、各部分の S と view。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

/-! ### 2〜3 行で送るメッセージ -/

/-- 2〜3 行で送るメッセージの列 -/
noncomputable def forwardMsgs (f : Nat) (p : Processor n Tx) : List (Msg n Tx) :=
  let nulls := (nullifyViews p.S).filter fun v =>
    decide (Nullified f p.S v ∧ ¬ Nullified f p.prevS v)
  let notas := (votedBlocks p.S).filter fun b =>
    decide (MNotarised f p.S b ∧ ¬ MNotarised f p.prevS b)
  (nulls.flatMap fun v => (leastNullifiers f p.S v).toList.map fun q => Msg.nullify q v)
  ++ (notas.flatMap fun b => (leastVoters f p.S b).toList.map fun q => Msg.vote q b)
  ++ (p.S.toList.filter fun m => match m with | .tx _ => decide (m ∉ p.prevS) | _ => false)

theorem forwardNew_eq (f : Nat) (i : Fin n) (p : Processor n Tx) :
    forwardNew f i p = disseminateAll i p (forwardMsgs f p) := rfl

theorem leastNullifiers_subset (f : Nat) (S : Finset (Msg n Tx)) (v : View) :
    leastNullifiers f S v ⊆ nullifiers S v := fun _ hq =>
  (Finset.mem_sort _).mp (List.mem_of_mem_take (List.mem_toFinset.mp hq))

theorem leastVoters_subset (f : Nat) (S : Finset (Msg n Tx)) (b : Block n Tx) :
    leastVoters f S b ⊆ voters S b := fun _ hq =>
  (Finset.mem_sort _).mp (List.mem_of_mem_take (List.mem_toFinset.mp hq))

theorem card_leastNullifiers {f : Nat} {S : Finset (Msg n Tx)} {v : View} (h : Nullified f S v) :
    (leastNullifiers f S v).card = 2 * f + 1 := by
  rw [leastNullifiers, List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).sublist
    (List.take_sublist _ _)), List.length_take, Finset.length_sort, Nat.min_eq_left h]

theorem card_leastVoters {f : Nat} {S : Finset (Msg n Tx)} {b : Block n Tx}
    (h : 2 * f + 1 ≤ (voters S b).card) : (leastVoters f S b).card = 2 * f + 1 := by
  rw [leastVoters, List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).sublist
    (List.take_sublist _ _)), List.length_take, Finset.length_sort, Nat.min_eq_left h]

theorem mem_S_of_mem_forwardMsgs {f : Nat} {p : Processor n Tx} {m : Msg n Tx}
    (h : m ∈ forwardMsgs f p) : m ∈ p.S := by
  simp only [forwardMsgs, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_map,
    Finset.mem_toList] at h
  rcases h with (⟨v, _, q, hq, rfl⟩ | ⟨b, _, q, hq, rfl⟩) | ⟨hm, _⟩
  · exact (Finset.mem_filter.mp (leastNullifiers_subset f _ _ hq)).2
  · exact (Finset.mem_filter.mp (leastVoters_subset f _ _ hq)).2
  · exact hm

/-! ### 部分ごとの入力状態と動作の列の分解 -/

section Stages

variable (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx)

/-- 各部分の後の局所状態で、次の部分の入力: st1 は 16〜21 行の後、st2 は 5〜7 行の後、st3 は 9〜11 行の後、
    st4 は 13〜14 行の後、st5 は 24〜28 行の後。最後に 2〜3 行が続く。 -/
noncomputable def st1 : Processor n Tx := (climb f i p).1
noncomputable def st2 : Processor n Tx := (propose f lead i (st1 f i p)).1
noncomputable def st3 : Processor n Tx := (voteProposal f lead i (st2 f lead i p)).1
noncomputable def st4 : Processor n Tx := (nullifyTimeout Δ i (st3 f lead i p)).1
noncomputable def st5 : Processor n Tx := (nullifyNoProgress f i (st4 f Δ lead i p)).1

/-- `Algo.step` の動作の列は、各部分の動作の列の連結。 -/
theorem step_eq_parts : step f Δ lead i p =
    (climb f i p).2 ++ (propose f lead i (st1 f i p)).2
      ++ (voteProposal f lead i (st2 f lead i p)).2 ++ (nullifyTimeout Δ i (st3 f lead i p)).2
      ++ (nullifyNoProgress f i (st4 f Δ lead i p)).2
      ++ (forwardNew f i (st5 f Δ lead i p)).2 := rfl

/-- 2〜3 行の転送を除いた動作の列 -/
noncomputable def innerActs : List (Action n Tx) :=
  (climb f i p).2 ++ (propose f lead i (st1 f i p)).2
    ++ (voteProposal f lead i (st2 f lead i p)).2 ++ (nullifyTimeout Δ i (st3 f lead i p)).2
    ++ (nullifyNoProgress f i (st4 f Δ lead i p)).2

theorem step_eq_innerActs : step f Δ lead i p =
    innerActs f Δ lead i p ++ (forwardNew f i (st5 f Δ lead i p)).2 := rfl

end Stages

/-! ### 19〜21 行の投票
`climb` の 19〜21 行で、投票するかしないかした直後の局所状態と動作の列。 -/

theorem mem_S_of_send_disseminate {i : Fin n} {p : Processor n Tx} {m m' : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (disseminate i p m').2) : m ∈ (disseminate i p m').1.S := by
  obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
  cases hm
  exact mem_S_disseminate_fst i p _

theorem ite_vote_view (i : Fin n) (p : Processor n Tx) (b : Block n Tx) :
    (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
      else (p, [])).1.view = p.view := by
  split_ifs
  · exact disseminate_view i p _
  · rfl

theorem ite_vote_progress_view (i : Fin n) (p : Processor n Tx) (b : Block n Tx) :
    (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
      else (p, [])).1.progress.view.val = p.view.val + 1 := by
  show (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
      else (p, [])).1.view.val + 1 = p.view.val + 1
  rw [ite_vote_view]

theorem S_subset_ite_vote (i : Fin n) (p : Processor n Tx) (b : Block n Tx) :
    p.S ⊆ (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
      else (p, [])).1.S := by
  split_ifs
  · exact S_subset_disseminate_fst i p _
  · exact Finset.Subset.refl _

theorem mem_S_ite_vote_or {i : Fin n} {p : Processor n Tx} {b : Block n Tx} {m : Msg n Tx}
    (h : m ∈ (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
      else (p, [])).1.S) :
    m ∈ p.S ∨ (m = Msg.vote i b ∧ Action.send (Msg.vote i b) i
      ∈ (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
        else (p, [])).2) := by
  split_ifs at h ⊢
  · exact (mem_S_disseminate_or i p _ h).imp_right fun h => ⟨h, mem_disseminate_snd.mpr ⟨i, rfl⟩⟩
  · exact Or.inl h

theorem send_ite_vote_eq {i : Fin n} {p : Processor n Tx} {b : Block n Tx} {m : Msg n Tx}
    {j : Fin n}
    (h : Action.send m j ∈ (if p.notarised = none ∧ p.nullified = false
      then disseminate i p (.vote i b) else (p, [])).2) :
    m = Msg.vote i b ∧ p.notarised = none ∧ p.nullified = false := by
  split_ifs at h with hg
  · obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
    cases hm
    exact ⟨rfl, hg⟩
  · simp at h

theorem mem_S_of_send_ite_vote {i : Fin n} {p : Processor n Tx} {b : Block n Tx} {m : Msg n Tx}
    {j : Fin n}
    (h : Action.send m j ∈ (if p.notarised = none ∧ p.nullified = false
      then disseminate i p (.vote i b) else (p, [])).2) :
    m ∈ (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
      else (p, [])).1.S := by
  split_ifs at h ⊢
  · exact mem_S_of_send_disseminate h
  · simp at h

theorem executeAll_ite_vote {i : Fin n} {p : Processor n Tx} {b : Block n Tx}
    (hb : containsBlock p.S b) :
    p.executeAll i (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
      else (p, [])).2
    = (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
      else (p, [])).1 := by
  split_ifs
  · exact executeAll_disseminate (Processor.canSend_vote hb)
  · rfl

theorem guardOK_ite_vote {i : Fin n} {p : Processor n Tx} {b : Block n Tx}
    (hb : containsBlock p.S b) :
    Processor.GuardOK i p (if p.notarised = none ∧ p.nullified = false
      then disseminate i p (.vote i b) else (p, [])).2 := by
  split_ifs
  · exact guardOK_disseminate (Processor.canSend_vote hb)
  · trivial

/-! ### 各部分で、返す局所状態は返す動作の畳み込み -/

theorem executeAll_forwardNew (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (forwardNew f i p).2 = (forwardNew f i p).1 := by
  rw [forwardNew_eq]
  exact executeAll_disseminateAll fun m hm => Processor.canSend_of_mem (mem_S_of_mem_forwardMsgs hm)

theorem executeAll_propose (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (propose f lead i p).2 = (propose f lead i p).1 := by
  unfold propose
  split_ifs
  · exact executeAll_disseminate (Processor.canSend_propose rfl)
  · rfl

theorem executeAll_voteProposal (f : Nat) (lead : View → Fin n) (i : Fin n)
    (p : Processor n Tx) :
    p.executeAll i (voteProposal f lead i p).2 = (voteProposal f lead i p).1 := by
  unfold voteProposal
  rcases hl : proposals lead p.S p.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · rfl
  · simp only
    split_ifs
    · have hb : b ∈ proposals lead p.S p.view := by rw [hl]; exact List.mem_singleton_self b
      exact executeAll_disseminate (Processor.canSend_vote (containsBlock_of_mem_proposals hb))
    · rfl
  · rfl

theorem executeAll_nullifyTimeout (Δ : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (nullifyTimeout Δ i p).2 = (nullifyTimeout Δ i p).1 := by
  unfold nullifyTimeout
  split_ifs
  · exact executeAll_disseminate Processor.canSend_nullify
  · rfl

theorem executeAll_climb (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (climb f i p).2 = (climb f i p).1 := by
  refine climb_induction f i ?_ ?_ ?_ p
  · intro p hN ih
    rw [climb_of_nullified i hN, Processor.executeAll_cons]
    exact ih
  · intro p hN hM ih
    rw [climb_of_mnotarised i hN hM]
    dsimp only
    have hb := containsBlock_of_mem_mNotarisedAt (List.head_mem hM)
    rw [Processor.executeAll_append, executeAll_ite_vote hb, Processor.executeAll_cons]
    exact ih
  · intro p hN hM
    rw [climb_of_not i fun h => h.elim hN hM]
    rfl

theorem executeAll_nullifyNoProgress (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (nullifyNoProgress f i p).2 = (nullifyNoProgress f i p).1 := by
  unfold nullifyNoProgress
  split_ifs
  · exact executeAll_disseminate Processor.canSend_nullify
  · rfl

/-- `Algo.step` の動作を畳み込んだ局所状態は、2〜3 行の後の局所状態。 -/
theorem executeAll_step (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (step f Δ lead i p) = (forwardNew f i (st5 f Δ lead i p)).1 := by
  simp only [step, st5, st4, st3, st2, st1, Processor.executeAll_append, executeAll_forwardNew,
    executeAll_propose, executeAll_voteProposal, executeAll_nullifyTimeout, executeAll_climb,
    executeAll_nullifyNoProgress]

/-! ### 各部分の send は、その時点の局所状態の `canSend` を満たす -/

theorem guardOK_forwardNew (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor.GuardOK i p (forwardNew f i p).2 := by
  rw [forwardNew_eq]
  exact guardOK_disseminateAll fun m hm => Processor.canSend_of_mem (mem_S_of_mem_forwardMsgs hm)

theorem guardOK_propose (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor.GuardOK i p (propose f lead i p).2 := by
  unfold propose
  split_ifs
  · exact guardOK_disseminate (Processor.canSend_propose rfl)
  · trivial

theorem guardOK_voteProposal (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor.GuardOK i p (voteProposal f lead i p).2 := by
  unfold voteProposal
  rcases hl : proposals lead p.S p.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · trivial
  · simp only
    split_ifs
    · have hb : b ∈ proposals lead p.S p.view := by rw [hl]; exact List.mem_singleton_self b
      exact guardOK_disseminate (Processor.canSend_vote (containsBlock_of_mem_proposals hb))
    · trivial
  · trivial

theorem guardOK_nullifyTimeout (Δ : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor.GuardOK i p (nullifyTimeout Δ i p).2 := by
  unfold nullifyTimeout
  split_ifs
  · exact guardOK_disseminate Processor.canSend_nullify
  · trivial

theorem guardOK_climb (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor.GuardOK i p (climb f i p).2 := by
  refine climb_induction f i ?_ ?_ ?_ p
  · intro p hN ih
    rw [climb_of_nullified i hN]
    exact Processor.GuardOK.progress_cons ih
  · intro p hN hM ih
    rw [climb_of_mnotarised i hN hM]
    dsimp only
    have hb := containsBlock_of_mem_mNotarisedAt (List.head_mem hM)
    refine Processor.GuardOK.append (guardOK_ite_vote hb) ?_
    rw [executeAll_ite_vote hb]
    exact Processor.GuardOK.progress_cons ih
  · intro p hN hM
    rw [climb_of_not i fun h => h.elim hN hM]
    trivial

theorem guardOK_nullifyNoProgress (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor.GuardOK i p (nullifyNoProgress f i p).2 := by
  unfold nullifyNoProgress
  split_ifs
  · exact guardOK_disseminate Processor.canSend_nullify
  · trivial

/-- `Algo.step` の各 send は、その時点の局所状態の `canSend` を満たす。 -/
theorem guardOK_step (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor.GuardOK i p (step f Δ lead i p) := by
  simp only [step]
  refine Processor.GuardOK.append (Processor.GuardOK.append (Processor.GuardOK.append
    (Processor.GuardOK.append (Processor.GuardOK.append (guardOK_climb f i p) ?_) ?_) ?_) ?_) ?_
    <;> simp only [Processor.executeAll_append, executeAll_climb, executeAll_propose,
      executeAll_voteProposal, executeAll_nullifyTimeout, executeAll_nullifyNoProgress]
  · exact guardOK_propose f lead i _
  · exact guardOK_voteProposal f lead i _
  · exact guardOK_nullifyTimeout Δ i _
  · exact guardOK_nullifyNoProgress f i _
  · exact guardOK_forwardNew f i _

/-! ### 各部分で S は減らない -/

theorem S_subset_disseminateAll_fst (i : Fin n) (p : Processor n Tx) (ms : List (Msg n Tx)) :
    p.S ⊆ (disseminateAll i p ms).1.S := by
  rw [disseminateAll_fst]
  induction ms generalizing p with
  | nil => exact Finset.Subset.refl _
  | cons m ms ih => exact (S_subset_disseminate_fst i p m).trans (ih _)

theorem mem_S_of_mem_disseminateAll_snd {i : Fin n} {p : Processor n Tx} {ms : List (Msg n Tx)}
    {m : Msg n Tx} {j : Fin n} (h : Action.send m j ∈ (disseminateAll i p ms).2) :
    m ∈ (disseminateAll i p ms).1.S := by
  rw [disseminateAll_fst]
  rw [disseminateAll_snd] at h
  induction ms generalizing p with
  | nil => simp at h
  | cons m' ms ih =>
    simp only [List.flatMap_cons, List.mem_append, List.foldl_cons] at h ⊢
    rcases h with h | h
    · rw [← disseminate_snd i p m'] at h
      obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
      cases hm
      exact S_subset_foldl_send_fst i ms _ (mem_S_disseminate_fst i p _)
    · exact ih h

theorem S_subset_propose (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (propose f lead i p).1.S := by
  unfold propose; split_ifs
  · exact S_subset_disseminate_fst i p _
  · exact Finset.Subset.refl _

theorem S_subset_voteProposal (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (voteProposal f lead i p).1.S := by
  unfold voteProposal
  rcases proposals lead p.S p.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · exact Finset.Subset.refl _
  · simp only; split_ifs
    · exact S_subset_disseminate_fst i p _
    · exact Finset.Subset.refl _
  · exact Finset.Subset.refl _

theorem S_subset_nullifyTimeout (Δ : Nat) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (nullifyTimeout Δ i p).1.S := by
  unfold nullifyTimeout; split_ifs
  · exact S_subset_disseminate_fst i p _
  · exact Finset.Subset.refl _

theorem S_subset_climb (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (climb f i p).1.S := by
  refine climb_induction f i ?_ ?_ ?_ p
  · intro p hN ih
    rw [climb_of_nullified i hN]
    exact ih
  · intro p hN hM ih
    rw [climb_of_mnotarised i hN hM]
    dsimp only
    exact (S_subset_ite_vote i p _).trans ih
  · intro p hN hM
    rw [climb_of_not i fun h => h.elim hN hM]

theorem S_subset_nullifyNoProgress (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (nullifyNoProgress f i p).1.S := by
  unfold nullifyNoProgress; split_ifs
  · exact S_subset_disseminate_fst i p _
  · exact Finset.Subset.refl _

theorem S_subset_forwardNew (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (forwardNew f i p).1.S := by
  rw [forwardNew_eq]; exact S_subset_disseminateAll_fst i p _

/-! #### 送ったメッセージはその部分の後の S にある -/

theorem mem_S_of_send_forwardNew {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (forwardNew f i p).2) : m ∈ (forwardNew f i p).1.S := by
  rw [forwardNew_eq] at h ⊢; exact mem_S_of_mem_disseminateAll_snd h

theorem mem_S_of_send_propose {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    {m : Msg n Tx} {j : Fin n} (h : Action.send m j ∈ (propose f lead i p).2) :
    m ∈ (propose f lead i p).1.S := by
  unfold propose at h ⊢; split_ifs at h ⊢
  · exact mem_S_of_send_disseminate h
  · simp at h

theorem mem_S_of_send_voteProposal {f : Nat} {lead : View → Fin n} {i : Fin n}
    {p : Processor n Tx} {m : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (voteProposal f lead i p).2) : m ∈ (voteProposal f lead i p).1.S := by
  unfold voteProposal at h ⊢
  generalize proposals lead p.S p.view = l at h ⊢
  rcases l with _ | ⟨b, _ | ⟨b', l⟩⟩
  · simp at h
  · simp only at h ⊢; split_ifs at h ⊢
    · exact mem_S_of_send_disseminate h
    · simp at h
  · simp at h

theorem mem_S_of_send_nullifyTimeout {Δ : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (nullifyTimeout Δ i p).2) :
    m ∈ (nullifyTimeout Δ i p).1.S := by
  unfold nullifyTimeout at h ⊢; split_ifs at h ⊢
  · exact mem_S_of_send_disseminate h
  · simp at h

theorem mem_S_of_send_climb {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (climb f i p).2) : m ∈ (climb f i p).1.S := by
  revert h
  refine climb_induction f i ?_ ?_ ?_ p
  · intro p hN ih h
    rw [climb_of_nullified i hN] at h ⊢
    simp only [List.mem_cons, reduceCtorEq, false_or] at h
    exact ih h
  · intro p hN hM ih h
    rw [climb_of_mnotarised i hN hM] at h ⊢
    dsimp only at h ⊢
    rcases List.mem_append.mp h with h | h
    · exact S_subset_climb f i _ (mem_S_of_send_ite_vote h)
    · simp only [List.mem_cons, reduceCtorEq, false_or] at h
      exact ih h
  · intro p hN hM h
    rw [climb_of_not i fun h => h.elim hN hM] at h
    simp at h

theorem mem_S_of_send_nullifyNoProgress {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (nullifyNoProgress f i p).2) :
    m ∈ (nullifyNoProgress f i p).1.S := by
  unfold nullifyNoProgress at h ⊢; split_ifs at h ⊢
  · exact mem_S_of_send_disseminate h
  · simp at h

/-- `Algo.step` が送るメッセージは、その動作をすべて実行した後の S にある。 -/
theorem mem_S_of_send_step {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    {m : Msg n Tx} {j : Fin n} (h : Action.send m j ∈ step f Δ lead i p) :
    m ∈ (p.executeAll i (step f Δ lead i p)).S := by
  rw [executeAll_step]
  simp only [step, List.mem_append] at h
  rcases h with (((((h | h) | h) | h) | h) | h)
  · exact S_subset_forwardNew _ _ _ (S_subset_nullifyNoProgress _ _ _ (S_subset_nullifyTimeout _ _ _
      (S_subset_voteProposal _ _ _ _ (S_subset_propose _ _ _ _ (mem_S_of_send_climb h)))))
  · exact S_subset_forwardNew _ _ _ (S_subset_nullifyNoProgress _ _ _ (S_subset_nullifyTimeout _ _ _
      (S_subset_voteProposal _ _ _ _ (mem_S_of_send_propose h))))
  · exact S_subset_forwardNew _ _ _ (S_subset_nullifyNoProgress _ _ _ (S_subset_nullifyTimeout _ _ _
      (mem_S_of_send_voteProposal h)))
  · exact S_subset_forwardNew _ _ _
      (S_subset_nullifyNoProgress _ _ _ (mem_S_of_send_nullifyTimeout h))
  · exact S_subset_forwardNew _ _ _ (mem_S_of_send_nullifyNoProgress h)
  · exact mem_S_of_send_forwardNew h

/-! #### 各部分の view・S -/

theorem disseminateAll_view (i : Fin n) (p : Processor n Tx) (ms : List (Msg n Tx)) :
    (disseminateAll i p ms).1.view = p.view := by
  rw [disseminateAll_fst]
  induction ms generalizing p with
  | nil => rfl
  | cons m ms ih => rw [List.foldl_cons, ih, disseminate_view]

theorem forwardNew_view (f : Nat) (i : Fin n) (p : Processor n Tx) :
    (forwardNew f i p).1.view = p.view := by
  rw [forwardNew_eq]; exact disseminateAll_view i p _

theorem propose_view (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (propose f lead i p).1.view = p.view := by
  unfold propose; split_ifs
  · exact disseminate_view i p _
  · rfl

theorem voteProposal_view (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (voteProposal f lead i p).1.view = p.view := by
  unfold voteProposal
  rcases proposals lead p.S p.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · rfl
  · simp only; split_ifs
    · exact disseminate_view i p _
    · rfl
  · rfl

theorem nullifyTimeout_view (Δ : Nat) (i : Fin n) (p : Processor n Tx) :
    (nullifyTimeout Δ i p).1.view = p.view := by
  unfold nullifyTimeout; split_ifs
  · exact disseminate_view i p _
  · rfl

theorem nullifyNoProgress_view (f : Nat) (i : Fin n) (p : Processor n Tx) :
    (nullifyNoProgress f i p).1.view = p.view := by
  unfold nullifyNoProgress; split_ifs
  · exact disseminate_view i p _
  · rfl

theorem disseminate_S_of_mem (i : Fin n) (q : Processor n Tx) {m : Msg n Tx} (hm : m ∈ q.S) :
    (disseminate i q m).1.S = q.S := by
  rw [disseminate_fst]
  generalize List.finRange n = l
  induction l generalizing q with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons]
    have hS : (q.send i m j).S = q.S := by
      rw [Processor.send_S]; split_ifs <;> simp [Finset.insert_eq_of_mem hm]
    rw [ih _ (hS ▸ hm), hS]

theorem forwardNew_S (f : Nat) (i : Fin n) (p : Processor n Tx) : (forwardNew f i p).1.S = p.S := by
  rw [forwardNew_eq, disseminateAll_fst]
  have key : ∀ (ms : List (Msg n Tx)) (q : Processor n Tx), (∀ m ∈ ms, m ∈ q.S) →
      (ms.foldl (fun p m => (disseminate i p m).1) q).S = q.S := by
    intro ms
    induction ms with
    | nil => intro q _; rfl
    | cons m ms ih =>
      intro q hq
      rw [List.foldl_cons]
      have hS := disseminate_S_of_mem i q (hq m (List.mem_cons_self ..))
      rw [ih _ (fun m' hm' => hS ▸ hq m' (List.mem_cons_of_mem _ hm')), hS]
  exact key _ p fun m hm => mem_S_of_mem_forwardMsgs hm

/-- 各部分の view、5〜7 行以降は変わらない -/
theorem st2_view (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st2 f lead i p).view = (st1 f i p).view := propose_view f lead i _

theorem st3_view (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st3 f lead i p).view = (st1 f i p).view := by
  simp only [st3]; rw [voteProposal_view, st2_view]

theorem st4_view (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st4 f Δ lead i p).view = (st1 f i p).view := by
  simp only [st4]; rw [nullifyTimeout_view, st3_view]

theorem st5_view (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st5 f Δ lead i p).view = (st1 f i p).view := by
  simp only [st5]; rw [nullifyNoProgress_view, st4_view]

/-- `Algo.step` の動作を畳み込んだ局所状態の view は、16〜21 行の後の view。 -/
theorem executeAll_step_view (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (p.executeAll i (step f Δ lead i p)).view = (st1 f i p).view := by
  rw [executeAll_step, forwardNew_view, st5_view]

/-- `Algo.step` の動作を畳み込んだ局所状態の S は、24〜28 行の後の S。 -/
theorem executeAll_step_S (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (p.executeAll i (step f Δ lead i p)).S = (st5 f Δ lead i p).S := by
  rw [executeAll_step, forwardNew_S]

end Algo

end Minimmit
