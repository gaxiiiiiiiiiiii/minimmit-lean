import Minimmit.Model.Algo
import Minimmit.Analysis.Transition

/-!
# Algorithm 1 の補題

`Algo.step` を段ごとに分け、各段が返す局所状態が、返す動作の列を `Processor.execute` で
畳み込んだものに等しいこと、送る message がすべてガードを通ること、票が出る条件を示す。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

/-! ### disseminate -/

theorem disseminate_snd (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    (disseminate i p m).2 = (List.finRange n).map (Action.send m) := by
  simp only [disseminate]
  suffices h : ∀ (l : List (Fin n)) (p : Processor n Tx) (acc : List (Action n Tx)),
      (l.foldl (fun (pa : Processor n Tx × List (Action n Tx)) j =>
        (pa.1.send i m j, pa.2 ++ [Action.send m j])) (p, acc)).2 = acc ++ l.map (Action.send m) by
    simpa using h (List.finRange n) p []
  intro l
  induction l with
  | nil => simp
  | cons j l ih => intro p acc; simp [ih]

theorem disseminate_fst (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    (disseminate i p m).1 = (List.finRange n).foldl (fun p j => p.send i m j) p := by
  simp only [disseminate]
  suffices h : ∀ (l : List (Fin n)) (p : Processor n Tx) (acc : List (Action n Tx)),
      (l.foldl (fun (pa : Processor n Tx × List (Action n Tx)) j =>
        (pa.1.send i m j, pa.2 ++ [Action.send m j])) (p, acc)).1
        = l.foldl (fun p j => p.send i m j) p by
    exact h (List.finRange n) p []
  intro l
  induction l with
  | nil => simp
  | cons j l ih => intro p acc; simp [ih]

theorem mem_disseminate_snd {i : Fin n} {p : Processor n Tx} {m : Msg n Tx} {a : Action n Tx} :
    a ∈ (disseminate i p m).2 ↔ ∃ j, a = Action.send m j := by
  simp [disseminate_snd, List.mem_finRange, eq_comm]

theorem S_subset_foldl_send (i : Fin n) (m : Msg n Tx) (l : List (Fin n)) (p : Processor n Tx) :
    p.S ⊆ (l.foldl (fun p j => p.send i m j) p).S := by
  induction l generalizing p with
  | nil => exact Finset.Subset.refl _
  | cons j l ih => exact (Processor.S_subset_send i p m j).trans (ih _)

theorem mem_S_send_self (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    m ∈ (p.send i m i).S := by
  cases m <;> simp [Processor.send]

/-- 送った message は自分にも送るので、送った後の S にある。 -/
theorem mem_S_disseminate_fst (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    m ∈ (disseminate i p m).1.S := by
  rw [disseminate_fst]
  have hi : i ∈ List.finRange n := List.mem_finRange i
  suffices h : ∀ (l : List (Fin n)) (p : Processor n Tx), i ∈ l →
      m ∈ (l.foldl (fun p j => p.send i m j) p).S by
    exact h _ _ hi
  intro l
  induction l with
  | nil => simp
  | cons j l ih =>
    intro p hj
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hj with rfl | hj
    · exact S_subset_foldl_send i m l _ (mem_S_send_self i p m)
    · exact ih _ hj

/-- ガードを通る message の disseminate は、動作の畳み込みと局所状態が一致する。 -/
theorem executeAll_disseminate {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    (h : m.signer = some i ∨ m ∈ p.S) :
    p.executeAll i (disseminate i p m).2 = (disseminate i p m).1 := by
  rw [disseminate_snd, disseminate_fst]
  suffices key : ∀ (l : List (Fin n)) (p : Processor n Tx), (m.signer = some i ∨ m ∈ p.S) →
      p.executeAll i (l.map (Action.send m)) = l.foldl (fun p j => p.send i m j) p by
    exact key _ _ h
  intro l
  induction l with
  | nil => intros; rfl
  | cons j l ih =>
    intro p h
    simp only [List.map_cons, Processor.executeAll_cons, List.foldl_cons, Processor.execute, h,
      if_true]
    exact ih _ (h.imp_right fun hm => Processor.S_subset_send i p m j hm)

/-! ### disseminateAll -/

theorem S_subset_disseminate_fst (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    p.S ⊆ (disseminate i p m).1.S := by
  rw [disseminate_fst]; exact S_subset_foldl_send i m _ p

private theorem disseminateAll_foldl (i : Fin n) (ms : List (Msg n Tx)) (p : Processor n Tx)
    (acc : List (Action n Tx)) :
    ms.foldl (fun (pa : Processor n Tx × List (Action n Tx)) m =>
        ((disseminate i pa.1 m).1, pa.2 ++ (disseminate i pa.1 m).2)) (p, acc)
      = (ms.foldl (fun p m => (disseminate i p m).1) p,
         acc ++ ms.flatMap fun m => (List.finRange n).map (Action.send m)) := by
  induction ms generalizing p acc with
  | nil => simp
  | cons m ms ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [disseminate_snd]

theorem disseminateAll_fst (i : Fin n) (p : Processor n Tx) (ms : List (Msg n Tx)) :
    (disseminateAll i p ms).1 = ms.foldl (fun p m => (disseminate i p m).1) p := by
  simp [disseminateAll, disseminateAll_foldl]

theorem disseminateAll_snd (i : Fin n) (p : Processor n Tx) (ms : List (Msg n Tx)) :
    (disseminateAll i p ms).2 = ms.flatMap fun m => (List.finRange n).map (Action.send m) := by
  simp [disseminateAll, disseminateAll_foldl]

theorem mem_disseminateAll_snd {i : Fin n} {p : Processor n Tx} {ms : List (Msg n Tx)}
    {a : Action n Tx} : a ∈ (disseminateAll i p ms).2 ↔ ∃ m ∈ ms, ∃ j, a = Action.send m j := by
  simp [disseminateAll_snd, List.mem_flatMap, List.mem_finRange, eq_comm]

theorem S_subset_foldl_send_fst (i : Fin n) (ms : List (Msg n Tx)) (p : Processor n Tx) :
    p.S ⊆ (ms.foldl (fun p m => (disseminate i p m).1) p).S := by
  induction ms generalizing p with
  | nil => exact Finset.Subset.refl _
  | cons m ms ih => exact (S_subset_disseminate_fst i p m).trans (ih _)

theorem executeAll_disseminateAll {i : Fin n} {p : Processor n Tx} {ms : List (Msg n Tx)}
    (h : ∀ m ∈ ms, m.signer = some i ∨ m ∈ p.S) :
    p.executeAll i (disseminateAll i p ms).2 = (disseminateAll i p ms).1 := by
  rw [disseminateAll_snd, disseminateAll_fst]
  revert h
  induction ms generalizing p with
  | nil => intro _; rfl
  | cons m ms ih =>
    intro h
    simp only [List.flatMap_cons, List.foldl_cons, Processor.executeAll_append]
    rw [← disseminate_snd i p m, executeAll_disseminate (h m (List.mem_cons_self ..))]
    exact ih fun m' hm' =>
      (h m' (List.mem_cons_of_mem _ hm')).imp_right fun hm => S_subset_disseminate_fst i p m hm

/-! ### 段ごとの分解
`Algo.step` の各段を名前付きの関数にする。本体は `Algo.step` と同じ。 -/

/-- 2〜3 行で送る message の列。 -/
noncomputable def forwardMsgs (f : Nat) (p : Processor n Tx) : List (Msg n Tx) :=
  let nulls := (nullifyViews p.S).filter fun v =>
    decide (Nullified f p.S v ∧ ¬ Nullified f p.prevS v)
  let notas := (votedBlocks p.S).filter fun b =>
    decide (MNotarised f p.S b ∧ ¬ MNotarised f p.prevS b)
  (nulls.flatMap fun v => p.S.toList.filter fun m => decide (∃ q, m = Msg.nullify q v))
  ++ (notas.flatMap fun b => p.S.toList.filter fun m => decide (∃ q, m = Msg.vote q b))
  ++ (p.S.toList.filter fun m => match m with | .tx _ => decide (m ∉ p.prevS) | _ => false)

theorem forwardNew_eq (f : Nat) (i : Fin n) (p : Processor n Tx) :
    forwardNew f i p = disseminateAll i p (forwardMsgs f p) := rfl

theorem mem_S_of_mem_forwardMsgs {f : Nat} {p : Processor n Tx} {m : Msg n Tx}
    (h : m ∈ forwardMsgs f p) : m ∈ p.S := by
  simp only [forwardMsgs, List.mem_append, List.mem_flatMap, List.mem_filter,
    Finset.mem_toList] at h
  rcases h with (⟨_, _, hm, _⟩ | ⟨_, _, hm, _⟩) | ⟨hm, _⟩ <;> exact hm

/-- 5〜7 行。 -/
noncomputable def propose (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if lead p.view = i ∧ p.proposed = false then
    let parent := selectParent f p.S p.view
    disseminate i p (.block i (.node p.view (payload p.S parent) parent))
  else (p, [])

open Classical in
/-- 9〜11 行。 -/
noncomputable def voteProposal (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  match proposals lead p.S p.view with
  | [b] =>
    if ValidProposal f lead p.S p.view b ∧ p.notarised = none ∧ p.nullified = false then
      disseminate i p (.vote i b)
    else (p, [])
  | _ => (p, [])

/-- 13〜14 行。 -/
def nullifyTimeout (Δ : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if p.timer = 2 * Δ ∧ p.nullified = false ∧ p.notarised = none then
    disseminate i p (.nullify i p.view)
  else (p, [])

/-- 16〜17 行。 -/
def advanceNull (f : Nat) (p : Processor n Tx) : Processor n Tx × List (Action n Tx) :=
  if Nullified f p.S p.view then (p.progress, [Action.progress]) else (p, [])

/-- 19〜21 行。 -/
noncomputable def advanceM (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  match mNotarisedAt f p.S p.view with
  | b :: _ =>
    let r :=
      if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
      else (p, [])
    (r.1.progress, r.2 ++ [Action.progress])
  | [] => (p, [])

open Classical in
/-- 24〜28 行。 -/
noncomputable def nullifyNoProgress (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if p.nullified = false ∧ p.notarised ≠ none ∧ NoProgress f p.S p.view p.notarised then
    disseminate i p (.nullify i p.view)
  else (p, [])

/-- `Algo.step` と同じ計算で、最後の局所状態も返す。 -/
noncomputable def stepPair (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  let r₁ := forwardNew f i p
  let r₂ := propose f lead i r₁.1
  let r₃ := voteProposal f lead i r₂.1
  let r₄ := nullifyTimeout Δ i r₃.1
  let r₅ := advanceNull f r₄.1
  let r₆ := advanceM f i r₅.1
  let r₇ := nullifyNoProgress f i r₆.1
  (r₇.1, r₁.2 ++ r₂.2 ++ r₃.2 ++ r₄.2 ++ r₅.2 ++ r₆.2 ++ r₇.2)

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

theorem executeAll_advanceNull (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (advanceNull f p).2 = (advanceNull f p).1 := by
  unfold advanceNull
  split_ifs <;> rfl

theorem executeAll_advanceM (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.executeAll i (advanceM f i p).2 = (advanceM f i p).1 := by
  unfold advanceM
  rcases mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · rfl
  · simp only [Processor.executeAll_append]
    split_ifs
    · rw [executeAll_disseminate (Or.inl rfl)]; rfl
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
    executeAll_voteProposal, executeAll_nullifyTimeout, executeAll_advanceNull,
    executeAll_advanceM, executeAll_nullifyNoProgress]

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

theorem S_subset_advanceNull (f : Nat) (p : Processor n Tx) : p.S ⊆ (advanceNull f p).1.S := by
  unfold advanceNull; split_ifs <;> exact Finset.Subset.refl _

theorem S_subset_advanceM (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (advanceM f i p).1.S := by
  unfold advanceM
  rcases mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · exact Finset.Subset.refl _
  · simp only; split_ifs
    · exact S_subset_disseminate_fst i p _
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

theorem mem_S_of_send_advanceNull {f : Nat} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (advanceNull f p).2) : m ∈ (advanceNull f p).1.S := by
  unfold advanceNull at h ⊢; split_ifs at h ⊢ <;> simp at h

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
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact S_subset_nullifyNoProgress _ _ _ (S_subset_advanceM _ _ _ (S_subset_advanceNull _ _
      (S_subset_nullifyTimeout _ _ _ (S_subset_voteProposal _ _ _ _ (S_subset_propose _ _ _ _
      (mem_S_of_send_forwardNew h))))))
  · exact S_subset_nullifyNoProgress _ _ _ (S_subset_advanceM _ _ _ (S_subset_advanceNull _ _
      (S_subset_nullifyTimeout _ _ _ (S_subset_voteProposal _ _ _ _
      (mem_S_of_send_propose h)))))
  · exact S_subset_nullifyNoProgress _ _ _ (S_subset_advanceM _ _ _ (S_subset_advanceNull _ _
      (S_subset_nullifyTimeout _ _ _ (mem_S_of_send_voteProposal h))))
  · exact S_subset_nullifyNoProgress _ _ _ (S_subset_advanceM _ _ _ (S_subset_advanceNull _ _
      (mem_S_of_send_nullifyTimeout h)))
  · exact S_subset_nullifyNoProgress _ _ _ (S_subset_advanceM _ _ _ (mem_S_of_send_advanceNull h))
  · exact S_subset_nullifyNoProgress _ _ _ (mem_S_of_send_advanceM h)
  · exact mem_S_of_send_nullifyNoProgress h

/-! ### 票の不変量
Lemma 5.1 の核。正直者 p_i の局所状態について、S にある自分の票と view・notarised の関係。 -/

/-- p_i の S にある自分の票についての不変量。 -/
structure VoteInv (i : Fin n) (p : Processor n Tx) : Prop where
  /-- 自分の票 (vote, c) が S にあれば、c は現在の view より前のブロックか、現在の view の
      ブロックで notarised に記録されている。 -/
  notar : ∀ c, Msg.vote i c ∈ p.S →
    c.view.val < p.view.val ∨ (c.view = p.view ∧ p.notarised = some c)
  /-- S にある自分の票で view が同じものは一致する。 -/
  unique : ∀ c c', Msg.vote i c ∈ p.S → Msg.vote i c' ∈ p.S → c.view = c'.view → c = c'

namespace VoteInv

variable {i : Fin n} {p : Processor n Tx}

/-- 自分の票でない message の送信は不変量を保つ。 -/
theorem send_of_not_vote (h : VoteInv i p) {m : Msg n Tx} (hm : ∀ b, m ≠ Msg.vote i b)
    (j : Fin n) : VoteInv i (p.send i m j) := by
  have hS : ∀ c, Msg.vote i c ∈ (p.send i m j).S → Msg.vote i c ∈ p.S := by
    intro c hc
    rw [Processor.send_S] at hc
    split_ifs at hc with hj
    · rcases Finset.mem_insert.mp hc with hc | hc
      · exact absurd hc.symm (hm c)
      · exact hc
    · exact hc
  have hn : (p.send i m j).notarised = p.notarised :=
    Processor.send_notarised_of_not_vote i p m j fun b hb => absurd hb (hm b)
  refine ⟨fun c hc => ?_, fun c c' hc hc' hv => h.unique c c' (hS c hc) (hS c' hc') hv⟩
  rw [Processor.send_view, hn]
  exact h.notar c (hS c hc)

/-- S にある message の再送は不変量を保つ。 -/
theorem send_of_mem (h : VoteInv i p) {m : Msg n Tx} (hm : m ∈ p.S) (j : Fin n) :
    VoteInv i (p.send i m j) := by
  have hS : (p.send i m j).S = p.S := by
    rw [Processor.send_S]; split_ifs <;> simp [Finset.insert_eq_of_mem hm]
  by_cases hv : ∃ b, m = Msg.vote i b
  · obtain ⟨b, rfl⟩ := hv
    refine ⟨fun c hc => ?_, fun c c' hc hc' hv => h.unique c c' (hS ▸ hc) (hS ▸ hc') hv⟩
    rw [hS] at hc
    rw [Processor.send_view, Processor.send_vote_notarised]
    rcases h.notar c hc with hlt | ⟨hce, hcn⟩
    · exact Or.inl hlt
    · right
      refine ⟨hce, ?_⟩
      split_ifs with hb
      · exact congrArg some (h.unique b c hm hc (hb.trans hce.symm))
      · exact hcn
  · exact h.send_of_not_vote (fun b hb => hv ⟨b, hb⟩) j

/-- notarised が ⊥ か、既に b のときの、現在の view のブロック b への票。 -/
theorem send_vote (h : VoteInv i p) {b : Block Tx} (hb : b.view = p.view)
    (hn : p.notarised = none ∨ p.notarised = some b) (j : Fin n) :
    VoteInv i (p.send i (Msg.vote i b) j) := by
  have hS : ∀ c, Msg.vote i c ∈ (p.send i (Msg.vote i b) j).S → c = b ∨ Msg.vote i c ∈ p.S := by
    intro c hc
    rw [Processor.send_S] at hc
    split_ifs at hc
    · rcases Finset.mem_insert.mp hc with hc | hc
      · exact Or.inl (by cases hc; rfl)
      · exact Or.inr hc
    · exact Or.inr hc
  -- 現在の view の自分の票が S にあれば、それは b
  have hcur : ∀ c, Msg.vote i c ∈ p.S → c.view = p.view → c = b := by
    intro c hc hcv
    rcases h.notar c hc with hlt | ⟨_, hcn⟩
    · rw [hcv] at hlt; exact absurd hlt (lt_irrefl _)
    · rcases hn with hn | hn
      · rw [hn] at hcn; cases hcn
      · rw [hn] at hcn; exact (Option.some.inj hcn).symm
  refine ⟨fun c hc => ?_, fun c c' hc hc' hv => ?_⟩
  · rw [Processor.send_view, Processor.send_vote_notarised, if_pos hb]
    rcases hS c hc with rfl | hc
    · exact Or.inr ⟨hb, rfl⟩
    · rcases h.notar c hc with hlt | ⟨hce, _⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨hce, congrArg some (hcur c hc hce).symm⟩
  · rcases hS c hc with hcb | hc
    · rcases hS c' hc' with hcb' | hc'
      · exact hcb.trans hcb'.symm
      · rw [hcb]
        exact (hcur c' hc' (hv.symm.trans (hcb ▸ hb))).symm
    · rcases hS c' hc' with hcb' | hc'
      · rw [hcb']
        exact hcur c hc (hv.trans (hcb' ▸ hb))
      · exact h.unique c c' hc hc' hv

omit [DecidableEq Tx] in
/-- 次の view へ進んでも不変量は保たれる。 -/
theorem progress (h : VoteInv i p) : VoteInv i p.progress := by
  refine ⟨fun c hc => ?_, fun c c' hc hc' hv => h.unique c c' hc hc' hv⟩
  left
  simp only [Processor.progress]
  rcases h.notar c hc with hlt | ⟨hce, _⟩
  · exact Nat.lt_succ_of_lt hlt
  · rw [hce]; exact Nat.lt_succ_self _

/-! #### 全員への送信 -/

theorem foldl_send_of_not_vote (h : VoteInv i p) {m : Msg n Tx} (hm : ∀ b, m ≠ Msg.vote i b)
    (l : List (Fin n)) : VoteInv i (l.foldl (fun p j => p.send i m j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih => exact ih (h.send_of_not_vote hm j)

theorem foldl_send_of_mem (h : VoteInv i p) {m : Msg n Tx} (hm : m ∈ p.S) (l : List (Fin n)) :
    VoteInv i (l.foldl (fun p j => p.send i m j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih => exact ih (h.send_of_mem hm j) (Processor.S_subset_send i p m j hm)

theorem foldl_send_vote (h : VoteInv i p) {b : Block Tx} (hb : b.view = p.view)
    (hn : p.notarised = none ∨ p.notarised = some b) (l : List (Fin n)) :
    VoteInv i (l.foldl (fun p j => p.send i (Msg.vote i b) j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih =>
    refine ih (h.send_vote hb hn j) (by rw [Processor.send_view]; exact hb) ?_
    right
    rw [Processor.send_vote_notarised, if_pos hb]

theorem disseminate_of_not_vote (h : VoteInv i p) {m : Msg n Tx} (hm : ∀ b, m ≠ Msg.vote i b) :
    VoteInv i (disseminate i p m).1 := by
  rw [disseminate_fst]; exact h.foldl_send_of_not_vote hm _

theorem disseminate_of_mem (h : VoteInv i p) {m : Msg n Tx} (hm : m ∈ p.S) :
    VoteInv i (disseminate i p m).1 := by
  rw [disseminate_fst]; exact h.foldl_send_of_mem hm _

theorem disseminate_vote (h : VoteInv i p) {b : Block Tx} (hb : b.view = p.view)
    (hn : p.notarised = none ∨ p.notarised = some b) :
    VoteInv i (disseminate i p (Msg.vote i b)).1 := by
  rw [disseminate_fst]; exact h.foldl_send_vote hb hn _

theorem disseminateAll_of_mem (h : VoteInv i p) {ms : List (Msg n Tx)} (hm : ∀ m ∈ ms, m ∈ p.S) :
    VoteInv i (disseminateAll i p ms).1 := by
  rw [disseminateAll_fst]
  induction ms generalizing p with
  | nil => exact h
  | cons m ms ih =>
    exact ih (h.disseminate_of_mem (hm m (List.mem_cons_self ..))) fun m' hm' =>
      S_subset_disseminate_fst i p m (hm m' (List.mem_cons_of_mem _ hm'))

/-! #### 各段 -/

theorem forwardNew (h : VoteInv i p) (f : Nat) : VoteInv i (forwardNew f i p).1 := by
  rw [forwardNew_eq]
  exact h.disseminateAll_of_mem fun m hm => mem_S_of_mem_forwardMsgs hm

theorem propose (h : VoteInv i p) (f : Nat) (lead : View → Fin n) :
    VoteInv i (propose f lead i p).1 := by
  unfold Algo.propose
  split_ifs
  · exact h.disseminate_of_not_vote fun _ h => by cases h
  · exact h

theorem voteProposal (h : VoteInv i p) (f : Nat) (lead : View → Fin n) :
    VoteInv i (voteProposal f lead i p).1 := by
  unfold Algo.voteProposal
  rcases proposals lead p.S p.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · exact h
  · simp only
    split_ifs with hg
    · exact h.disseminate_vote hg.1.view (Or.inl hg.2.1)
    · exact h
  · exact h

theorem nullifyTimeout (h : VoteInv i p) (Δ : Nat) : VoteInv i (nullifyTimeout Δ i p).1 := by
  unfold Algo.nullifyTimeout
  split_ifs
  · exact h.disseminate_of_not_vote fun _ h => by cases h
  · exact h

theorem advanceNull (h : VoteInv i p) (f : Nat) : VoteInv i (advanceNull f p).1 := by
  unfold Algo.advanceNull
  split_ifs
  · exact h.progress
  · exact h

theorem advanceM (h : VoteInv i p) (f : Nat) : VoteInv i (advanceM f i p).1 := by
  unfold Algo.advanceM
  rcases hm : mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · exact h
  · simp only
    split_ifs with hg
    · exact (h.disseminate_vote (mem_mNotarisedAt (hm ▸ List.mem_cons_self ..)).1
        (Or.inl hg.1)).progress
    · exact h.progress

theorem nullifyNoProgress (h : VoteInv i p) (f : Nat) :
    VoteInv i (nullifyNoProgress f i p).1 := by
  unfold Algo.nullifyNoProgress
  split_ifs
  · exact h.disseminate_of_not_vote fun _ h => by cases h
  · exact h

omit [DecidableEq Tx] in
/-- tick は不変量を保つ。 -/
theorem tick (h : VoteInv i p) (S₀ : Finset (Msg n Tx)) : VoteInv i (p.tick S₀) :=
  ⟨fun c hc => h.notar c hc, fun c c' hc hc' hv => h.unique c c' hc hc' hv⟩

omit [DecidableEq Tx] in
/-- S が増えても、増えた分に自分の票が無ければ不変量は保たれる。 -/
theorem of_sgrows (h : VoteInv i p) {q : Processor n Tx} (hg : p.SGrows q)
    (hv : ∀ c, Msg.vote i c ∈ q.S → Msg.vote i c ∈ p.S) : VoteInv i q := by
  refine ⟨fun c hc => ?_, fun c c' hc hc' hve => h.unique c c' (hv c hc) (hv c' hc') hve⟩
  rw [hg.view, hg.notarised]
  exact h.notar c (hv c hc)

/-- Algorithm 1 の 1 スロット分の動作は不変量を保つ。 -/
theorem stepPair (h : VoteInv i p) (f Δ : Nat) (lead : View → Fin n) :
    VoteInv i (stepPair f Δ lead i p).1 :=
  (((((((h.forwardNew f).propose f lead).voteProposal f lead).nullifyTimeout Δ).advanceNull f
    ).advanceM f).nullifyNoProgress f)

end VoteInv

end Algo

end Minimmit
