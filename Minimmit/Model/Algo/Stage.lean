import Minimmit.Model.Algo.Disseminate

/-!
# Algorithm 1 の段ごとの分解

`Algo.step` を段（16〜21 行、5〜7 行、9〜11 行、13〜14 行、24〜28 行、2〜3 行）に分け、
各段の入力状態 st1〜st5、動作列の畳み込み、各段の S と view。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

/-! ### 段ごとの分解
`Algo.step` の各段を名前付きの関数にする。本体は `Algo.step` と同じ。 -/

/-- 2〜3 行で送る message の列 -/
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

theorem leastVoters_subset (f : Nat) (S : Finset (Msg n Tx)) (b : Block Tx) :
    leastVoters f S b ⊆ voters S b := fun _ hq =>
  (Finset.mem_sort _).mp (List.mem_of_mem_take (List.mem_toFinset.mp hq))

theorem card_leastNullifiers {f : Nat} {S : Finset (Msg n Tx)} {v : View} (h : Nullified f S v) :
    (leastNullifiers f S v).card = 2 * f + 1 := by
  rw [leastNullifiers, List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).sublist
    (List.take_sublist _ _)), List.length_take, Finset.length_sort, Nat.min_eq_left h]

theorem card_leastVoters {f : Nat} {S : Finset (Msg n Tx)} {b : Block Tx}
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

/-- 5〜7 行 -/
noncomputable def propose (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if lead p.view = i ∧ p.proposed = false then
    let parent := selectParent f p.S p.view
    disseminate i p (.block i (.node p.view (payload p.S parent) parent))
  else (p, [])

open Classical in
/-- 9〜11 行 -/
noncomputable def voteProposal (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  match proposals lead p.S p.view with
  | [b] =>
    if ValidProposal f lead p.S p.view b ∧ p.notarised = none ∧ p.nullified = false then
      disseminate i p (.vote i b)
    else (p, [])
  | _ => (p, [])

/-- 13〜14 行 -/
def nullifyTimeout (Δ : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if p.timer = 2 * Δ ∧ p.nullified = false ∧ p.notarised = none then
    disseminate i p (.nullify i p.view)
  else (p, [])

/-- 19〜21 行、`advanceOnce` の現在の view の nullification がない側 -/
noncomputable def advanceM (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  match mNotarisedAt f p.S p.view with
  | b :: _ =>
    let r :=
      if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
      else (p, [])
    (r.1.progress, r.2 ++ [Action.progress])
  | [] => (p, [])

theorem advanceOnce_eq (f : Nat) (i : Fin n) (p : Processor n Tx) :
    advanceOnce f i p
      = if Nullified f p.S p.view then (p.progress, [Action.progress]) else advanceM f i p := rfl

open Classical in
/-- 24〜28 行 -/
noncomputable def nullifyNoProgress (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if p.nullified = false ∧ p.notarised ≠ none ∧ NoProgress f p.S p.view p.notarised then
    disseminate i p (.nullify i p.view)
  else (p, [])

/-- `Algo.step` と同じ計算で、最後の局所状態も返す。 -/
noncomputable def stepPair (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  let r₁ := climb f i (maxView p.S + 1) p
  let r₂ := propose f lead i r₁.1
  let r₃ := voteProposal f lead i r₂.1
  let r₄ := nullifyTimeout Δ i r₃.1
  let r₅ := nullifyNoProgress f i r₄.1
  let r₆ := forwardNew f i r₅.1
  (r₆.1, r₁.2 ++ r₂.2 ++ r₃.2 ++ r₄.2 ++ r₅.2 ++ r₆.2)

theorem step_eq_stepPair (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Algo.step f Δ lead i p = (stepPair f Δ lead i p).2 := rfl

/-! ### 各段で、返す局所状態は返す動作の畳み込み -/

theorem executeAll_forwardNew (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (forwardNew f i p).2 = (forwardNew f i p).1 := by
  rw [forwardNew_eq]
  exact executeAll_disseminateAll fun m hm => Or.inr (mem_S_of_mem_forwardMsgs hm)

theorem executeAll_propose (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (propose f lead i p).2 = (propose f lead i p).1 := by
  unfold propose
  split_ifs
  · exact executeAll_disseminate (Or.inl rfl)
  · rfl

theorem executeAll_voteProposal (f : Nat) (lead : View → Fin n) (i : Fin n)
    (p : Processor n Tx) :
    p.executeAll i (voteProposal f lead i p).2 = (voteProposal f lead i p).1 := by
  unfold voteProposal
  rcases proposals lead p.S p.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · rfl
  · simp only
    split_ifs
    · exact executeAll_disseminate (Or.inl rfl)
    · rfl
  · rfl

theorem executeAll_nullifyTimeout (Δ : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (nullifyTimeout Δ i p).2 = (nullifyTimeout Δ i p).1 := by
  unfold nullifyTimeout
  split_ifs
  · exact executeAll_disseminate (Or.inl rfl)
  · rfl

theorem executeAll_advanceM (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (advanceM f i p).2 = (advanceM f i p).1 := by
  unfold advanceM
  rcases mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · rfl
  · simp only [Processor.executeAll_append]
    split_ifs
    · rw [executeAll_disseminate (Or.inl rfl)]; rfl
    · rfl

theorem executeAll_advanceOnce (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (advanceOnce f i p).2 = (advanceOnce f i p).1 := by
  rw [advanceOnce_eq]
  split_ifs
  · rfl
  · exact executeAll_advanceM f i p

theorem executeAll_climb (f : Nat) (i : Fin n) (fuel : Nat) (p : Processor n Tx) :
    p.executeAll i (climb f i fuel p).2 = (climb f i fuel p).1 := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    simp only [climb]
    split_ifs
    · simp only [Processor.executeAll_append, executeAll_advanceOnce, ih]
    · rfl

theorem executeAll_nullifyNoProgress (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (nullifyNoProgress f i p).2 = (nullifyNoProgress f i p).1 := by
  unfold nullifyNoProgress
  split_ifs
  · exact executeAll_disseminate (Or.inl rfl)
  · rfl

/-- `Algo.step` の動作を畳み込んだ局所状態は、`stepPair` が返す局所状態。 -/
theorem executeAll_step (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (Algo.step f Δ lead i p) = (stepPair f Δ lead i p).1 := by
  rw [step_eq_stepPair]
  simp only [stepPair, Processor.executeAll_append, executeAll_forwardNew, executeAll_propose,
    executeAll_voteProposal, executeAll_nullifyTimeout, executeAll_climb,
    executeAll_nullifyNoProgress]

/-! ### 各段で送る message は、その段の後の S にある -/

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

theorem mem_mNotarisedAt {f : Nat} {S : Finset (Msg n Tx)} {v : View} {b : Block Tx}
    (h : b ∈ mNotarisedAt f S v) : b.view = v ∧ MNotarised f S b := by
  simp only [mNotarisedAt, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

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

theorem S_subset_advanceM (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (advanceM f i p).1.S := by
  unfold advanceM
  rcases mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · exact Finset.Subset.refl _
  · simp only; split_ifs
    · exact S_subset_disseminate_fst i p _
    · exact Finset.Subset.refl _

theorem S_subset_advanceOnce (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (advanceOnce f i p).1.S := by
  rw [advanceOnce_eq]; split_ifs
  · exact Finset.Subset.refl _
  · exact S_subset_advanceM f i p

theorem S_subset_climb (f : Nat) (i : Fin n) (fuel : Nat) (p : Processor n Tx) :
    p.S ⊆ (climb f i fuel p).1.S := by
  induction fuel generalizing p with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
    simp only [climb]; split_ifs
    · exact (S_subset_advanceOnce f i p).trans (ih _)
    · exact Finset.Subset.refl _

theorem S_subset_nullifyNoProgress (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (nullifyNoProgress f i p).1.S := by
  unfold nullifyNoProgress; split_ifs
  · exact S_subset_disseminate_fst i p _
  · exact Finset.Subset.refl _

theorem S_subset_forwardNew (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (forwardNew f i p).1.S := by
  rw [forwardNew_eq]; exact S_subset_disseminateAll_fst i p _

/-! #### 送った message はその段の後の S にある -/

theorem mem_S_of_send_disseminate {i : Fin n} {p : Processor n Tx} {m m' : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (disseminate i p m').2) : m ∈ (disseminate i p m').1.S := by
  obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
  cases hm
  exact mem_S_disseminate_fst i p _

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

theorem mem_S_of_send_advanceM {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (advanceM f i p).2) : m ∈ (advanceM f i p).1.S := by
  unfold advanceM at h ⊢
  generalize mNotarisedAt f p.S p.view = l at h ⊢
  rcases l with _ | ⟨b, l⟩
  · simp at h
  · simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h
    simp only
    split_ifs at h ⊢
    · exact mem_S_of_send_disseminate h
    · simp at h

theorem mem_S_of_send_advanceOnce {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (advanceOnce f i p).2) : m ∈ (advanceOnce f i p).1.S := by
  rw [advanceOnce_eq] at h ⊢; split_ifs at h ⊢
  · simp at h
  · exact mem_S_of_send_advanceM h

theorem mem_S_of_send_climb {f : Nat} {i : Fin n} {fuel : Nat} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (climb f i fuel p).2) : m ∈ (climb f i fuel p).1.S := by
  induction fuel generalizing p with
  | zero => simp [climb] at h
  | succ fuel ih =>
    simp only [climb] at h ⊢; split_ifs at h ⊢
    · rcases List.mem_append.mp h with h | h
      · exact S_subset_climb f i fuel _ (mem_S_of_send_advanceOnce h)
      · exact ih h
    · simp at h

theorem mem_S_of_send_nullifyNoProgress {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (nullifyNoProgress f i p).2) :
    m ∈ (nullifyNoProgress f i p).1.S := by
  unfold nullifyNoProgress at h ⊢; split_ifs at h ⊢
  · exact mem_S_of_send_disseminate h
  · simp at h

/-- `Algo.step` が送る message は、その動作をすべて実行した後の S にある。 -/
theorem mem_S_of_send_step {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    {m : Msg n Tx} {j : Fin n} (h : Action.send m j ∈ Algo.step f Δ lead i p) :
    m ∈ (stepPair f Δ lead i p).1.S := by
  rw [step_eq_stepPair] at h
  simp only [stepPair, List.mem_append] at h ⊢
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


/-! ### 段ごとの入力状態と、送信の出所 -/

section Stages

variable (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx)

/-- 各段の入力となる局所状態: st1 は 16〜21 行の後、st2 は 5〜7 行の後、st3 は 9〜11 行の後、
    st4 は 13〜14 行の後、st5 は 24〜28 行の後。最後に 2〜3 行が続く。 -/
noncomputable def st1 : Processor n Tx := (climb f i (maxView p.S + 1) p).1
noncomputable def st2 : Processor n Tx := (propose f lead i (st1 f i p)).1
noncomputable def st3 : Processor n Tx := (voteProposal f lead i (st2 f lead i p)).1
noncomputable def st4 : Processor n Tx := (nullifyTimeout Δ i (st3 f lead i p)).1
noncomputable def st5 : Processor n Tx := (nullifyNoProgress f i (st4 f Δ lead i p)).1

theorem stepPair_snd : (stepPair f Δ lead i p).2 =
    (climb f i (maxView p.S + 1) p).2 ++ (propose f lead i (st1 f i p)).2
      ++ (voteProposal f lead i (st2 f lead i p)).2 ++ (nullifyTimeout Δ i (st3 f lead i p)).2
      ++ (nullifyNoProgress f i (st4 f Δ lead i p)).2
      ++ (forwardNew f i (st5 f Δ lead i p)).2 := rfl

theorem stepPair_fst : (stepPair f Δ lead i p).1 = (forwardNew f i (st5 f Δ lead i p)).1 := rfl

/-- 2〜3 行の転送を除いた動作の列 -/
noncomputable def innerActs : List (Action n Tx) :=
  (climb f i (maxView p.S + 1) p).2 ++ (propose f lead i (st1 f i p)).2
    ++ (voteProposal f lead i (st2 f lead i p)).2 ++ (nullifyTimeout Δ i (st3 f lead i p)).2
    ++ (nullifyNoProgress f i (st4 f Δ lead i p)).2

theorem stepPair_snd' : (stepPair f Δ lead i p).2 =
    innerActs f Δ lead i p ++ (forwardNew f i (st5 f Δ lead i p)).2 := rfl

end Stages

/-! #### 各段の view・S -/

theorem disseminate_view (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    (disseminate i p m).1.view = p.view := by
  rw [disseminate_fst]
  induction List.finRange n generalizing p with
  | nil => rfl
  | cons j l ih => rw [List.foldl_cons, ih, Processor.send_view]

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

theorem advanceM_view (f : Nat) (i : Fin n) (p : Processor n Tx) :
    (advanceM f i p).1.view = p.view ∨ (advanceM f i p).1.view.val = p.view.val + 1 := by
  unfold advanceM
  rcases mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · exact Or.inl rfl
  · simp only
    split_ifs
    · right; simp [Processor.progress, disseminate_view]
    · right; simp [Processor.progress]

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

/-- 各段の view、5〜7 行以降は変わらない -/
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

theorem stepPair_view (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (stepPair f Δ lead i p).1.view = (st1 f i p).view := by
  rw [stepPair_fst, forwardNew_view, st5_view]

theorem advanceM_eq_of_nil {f : Nat} {i : Fin n} {q : Processor n Tx}
    (h : mNotarisedAt f q.S q.view = []) : (advanceM f i q).1 = q := by
  unfold advanceM; rw [h]

theorem advanceM_view_succ_of_ne_nil {f : Nat} {i : Fin n} {q : Processor n Tx}
    (h : mNotarisedAt f q.S q.view ≠ []) : (advanceM f i q).1.view.val = q.view.val + 1 := by
  unfold advanceM
  generalize hl : mNotarisedAt f q.S q.view = l at h ⊢
  rcases l with _ | ⟨b, l⟩
  · exact absurd rfl h
  · simp only
    split_ifs
    · simp [Processor.progress, disseminate_view]
    · simp [Processor.progress]

end Algo

end Minimmit
