import Minimmit.Model.Algo
import Minimmit.Analysis.Transition
import Minimmit.Analysis.Certificate

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

/-! ### 正直者の局所状態の不変量
Lemma 5.1・5.3 の核。S にある自分の票・nullify と、view・notarised・nullified の関係。 -/

/-- 送信の途中（全員へ送る途中）でも保たれる部分。 -/
structure PreInv (f : Nat) (i : Fin n) (p : Processor n Tx) : Prop where
  /-- view は 1 以上。 -/
  view_pos : 1 ≤ p.view.val
  /-- 自分の票 (vote, c) が S にあれば、c は view 1 以上のブロックで、現在の view より前の
      ものか、現在の view のもので notarised に記録されている。 -/
  notar : ∀ c, Msg.vote i c ∈ p.S →
    1 ≤ c.view.val ∧ (c.view.val < p.view.val ∨ (c.view = p.view ∧ p.notarised = some c))
  /-- S にある自分の票で view が同じものは一致する。 -/
  unique : ∀ c c', Msg.vote i c ∈ p.S → Msg.vote i c' ∈ p.S → c.view = c'.view → c = c'
  /-- notarised のブロックは現在の view。 -/
  notar_view : ∀ c, p.notarised = some c → c.view = p.view
  /-- 自分の nullify(w) が S にあれば、1 ≤ w ≤ 現在の view。 -/
  null_view : ∀ w, Msg.nullify i w ∈ p.S → 1 ≤ w.val ∧ w.val ≤ p.view.val
  /-- 自分の現在の view の nullify が S にあれば nullified。 -/
  null_flag : Msg.nullify i p.view ∈ p.S → p.nullified = true
  /-- 自分の nullify(w) と、view w のブロック c への自分の票が両方 S にあるなら、
      S は view w で c 以外への進捗のなさの証拠を含む（24〜28 行で送った）。 -/
  null_vote : ∀ w c, Msg.nullify i w ∈ p.S → Msg.vote i c ∈ p.S → c.view = w →
    NoProgress f p.S w (some c)

/-- 正直者の局所状態の不変量。 -/
structure LocalInv (f : Nat) (i : Fin n) (p : Processor n Tx) : Prop extends PreInv f i p where
  /-- notarised のブロックへの自分の票は S にある。 -/
  notar_mem : ∀ c, p.notarised = some c → Msg.vote i c ∈ p.S
  /-- nullified なら、現在の view の自分の nullify は S にある。 -/
  null_mem : p.nullified = true → Msg.nullify i p.view ∈ p.S

namespace PreInv

variable {f : Nat} {i : Fin n} {p : Processor n Tx}

omit [DecidableEq Tx] in
/-- 関係する欄が等しければ移る。 -/
theorem congr (h : PreInv f i p) {q : Processor n Tx} (hv : q.view = p.view)
    (hn : q.notarised = p.notarised) (hnl : q.nullified = p.nullified) (hS : q.S = p.S) :
    PreInv f i q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]; exact h.view_pos
  · intro c hc; rw [hS] at hc; rw [hv, hn]; exact h.notar c hc
  · intro c c' hc hc'; rw [hS] at hc hc'; exact h.unique c c' hc hc'
  · intro c hc; rw [hn] at hc; rw [hv]; exact h.notar_view c hc
  · intro w hw; rw [hS] at hw; rw [hv]; exact h.null_view w hw
  · intro hw; rw [hv, hS] at hw; rw [hnl]; exact h.null_flag hw
  · intro w c hw hc hcw; rw [hS] at hw hc ⊢; exact h.null_vote w c hw hc hcw

omit [DecidableEq Tx] in
/-- view・notarised・nullified が変わらず S が増えても、増えた分に自分の票と nullify が
    無ければ保たれる。 -/
theorem of_grow (h : PreInv f i p) {q : Processor n Tx} (hv : q.view = p.view)
    (hn : q.notarised = p.notarised) (hnl : q.nullified = p.nullified) (hS : p.S ⊆ q.S)
    (hvote : ∀ c, Msg.vote i c ∈ q.S → Msg.vote i c ∈ p.S)
    (hnull : ∀ w, Msg.nullify i w ∈ q.S → Msg.nullify i w ∈ p.S) : PreInv f i q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]; exact h.view_pos
  · intro c hc; rw [hv, hn]; exact h.notar c (hvote c hc)
  · intro c c' hc hc'; exact h.unique c c' (hvote c hc) (hvote c' hc')
  · intro c hc; rw [hn] at hc; rw [hv]; exact h.notar_view c hc
  · intro w hw; rw [hv]; exact h.null_view w (hnull w hw)
  · intro hw; rw [hv] at hw; rw [hnl]; exact h.null_flag (hnull _ hw)
  · intro w c hw hc hcw; exact (h.null_vote w c (hnull w hw) (hvote c hc) hcw).mono hS

omit [DecidableEq Tx] in
theorem of_sgrows (h : PreInv f i p) {q : Processor n Tx} (hg : p.SGrows q)
    (hvote : ∀ c, Msg.vote i c ∈ q.S → Msg.vote i c ∈ p.S)
    (hnull : ∀ w, Msg.nullify i w ∈ q.S → Msg.nullify i w ∈ p.S) : PreInv f i q :=
  h.of_grow hg.view hg.notarised hg.nullified hg.S hvote hnull

theorem mem_S_send_iff_of_ne (i : Fin n) (p : Processor n Tx) {m m' : Msg n Tx} (j : Fin n)
    (hne : m' ≠ m) : m' ∈ (p.send i m j).S ↔ m' ∈ p.S := by
  rw [Processor.send_S]
  split_ifs
  · simp [Finset.mem_insert, hne]
  · exact Iff.rfl

/-- 自分の票でも自分の nullify でもない message の送信は不変量を保つ。 -/
theorem send_of_not_own (h : PreInv f i p) {m : Msg n Tx} (hv : ∀ b, m ≠ Msg.vote i b)
    (hn : ∀ v, m ≠ Msg.nullify i v) (j : Fin n) : PreInv f i (p.send i m j) := by
  refine h.of_grow (Processor.send_view i p m j)
    (Processor.send_notarised_of_not_vote i p m j fun b hb => absurd hb (hv b))
    (Processor.send_nullified_of_not_nullify i p m j fun v hv' => absurd hv' (hn v))
    (Processor.S_subset_send i p m j) (fun c hc => ?_) (fun w hw => ?_)
  · exact (mem_S_send_iff_of_ne i p j fun h' => hv c h'.symm).mp hc
  · exact (mem_S_send_iff_of_ne i p j fun h' => hn w h'.symm).mp hw

/-- S にある message の再送は、view・notarised・nullified・S を変えない。 -/
theorem send_of_mem_eq (h : PreInv f i p) {m : Msg n Tx} (hm : m ∈ p.S) (j : Fin n) :
    (p.send i m j).notarised = p.notarised ∧ (p.send i m j).nullified = p.nullified
      ∧ (p.send i m j).S = p.S := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases hv : ∃ b, m = Msg.vote i b
    · obtain ⟨b, rfl⟩ := hv
      rw [Processor.send_vote_notarised]
      split_ifs with hb
      · exact ((h.notar b hm).2.resolve_left (by rw [hb]; exact lt_irrefl _)).2.symm
      · rfl
    · exact Processor.send_notarised_of_not_vote i p m j fun b hb => absurd ⟨b, hb⟩ hv
  · by_cases hn : ∃ v, m = Msg.nullify i v
    · obtain ⟨v, rfl⟩ := hn
      rw [Processor.send_nullify_nullified]
      split_ifs with hv
      · subst hv; exact (h.null_flag hm).symm
      · rfl
    · exact Processor.send_nullified_of_not_nullify i p m j fun v hv => absurd ⟨v, hv⟩ hn
  · rw [Processor.send_S]; split_ifs <;> simp [Finset.insert_eq_of_mem hm]

theorem send_of_mem (h : PreInv f i p) {m : Msg n Tx} (hm : m ∈ p.S) (j : Fin n) :
    PreInv f i (p.send i m j) :=
  let ⟨hn, hnl, hS⟩ := h.send_of_mem_eq hm j
  h.congr (Processor.send_view i p m j) hn hnl hS

/-- 現在の view のブロック b への自分の票。notarised が ⊥ か既に b で、現在の view の
    nullify を送っていないとき。 -/
theorem send_vote (h : PreInv f i p) {b : Block Tx} (hb : b.view = p.view)
    (hn : p.notarised = none ∨ p.notarised = some b) (hnn : Msg.nullify i p.view ∉ p.S)
    (j : Fin n) : PreInv f i (p.send i (Msg.vote i b) j) := by
  have hS : ∀ c, Msg.vote i c ∈ (p.send i (Msg.vote i b) j).S → c = b ∨ Msg.vote i c ∈ p.S := by
    intro c hc
    rw [Processor.send_S] at hc
    split_ifs at hc
    · rcases Finset.mem_insert.mp hc with hc | hc
      · exact Or.inl (by cases hc; rfl)
      · exact Or.inr hc
    · exact Or.inr hc
  have hN : ∀ w, Msg.nullify i w ∈ (p.send i (Msg.vote i b) j).S → Msg.nullify i w ∈ p.S :=
    fun w hw => (mem_S_send_iff_of_ne i p j (by simp)).mp hw
  have hcur : ∀ c, Msg.vote i c ∈ p.S → c.view = p.view → c = b := by
    intro c hc hcv
    rcases (h.notar c hc).2 with hlt | ⟨_, hcn⟩
    · rw [hcv] at hlt; exact absurd hlt (lt_irrefl _)
    · rcases hn with hn | hn
      · rw [hn] at hcn; cases hcn
      · rw [hn] at hcn; exact (Option.some.inj hcn).symm
  have hview := Processor.send_view i p (Msg.vote i b) j
  have hnot := Processor.send_vote_notarised i p b j
  rw [if_pos hb] at hnot
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hview]; exact h.view_pos
  · intro c hc
    rw [hview, hnot]
    rcases hS c hc with rfl | hc
    · exact ⟨by rw [hb]; exact h.view_pos, Or.inr ⟨hb, rfl⟩⟩
    · obtain ⟨hpos, hlt | ⟨hce, _⟩⟩ := h.notar c hc
      · exact ⟨hpos, Or.inl hlt⟩
      · exact ⟨hpos, Or.inr ⟨hce, congrArg some (hcur c hc hce).symm⟩⟩
  · intro c c' hc hc' hv
    rcases hS c hc with hcb | hc
    · rcases hS c' hc' with hcb' | hc'
      · exact hcb.trans hcb'.symm
      · rw [hcb]; exact (hcur c' hc' (hv.symm.trans (hcb ▸ hb))).symm
    · rcases hS c' hc' with hcb' | hc'
      · rw [hcb']; exact hcur c hc (hv.trans (hcb' ▸ hb))
      · exact h.unique c c' hc hc' hv
  · intro c hc; rw [hnot] at hc; rw [hview, ← Option.some.inj hc]; exact hb
  · intro w hw; rw [hview]; exact h.null_view w (hN w hw)
  · intro hw; rw [hview] at hw; exact absurd (hN _ hw) hnn
  · intro w c hw hc hcw
    have hw' := hN w hw
    rcases hS c hc with rfl | hc
    · have hwv : w = p.view := hcw.symm.trans hb
      rw [hwv] at hw'
      exact absurd hw' hnn
    · exact (h.null_vote w c hw' hc hcw).mono (Processor.S_subset_send i p _ j)

/-- 現在の view の nullify。notarised が ⊥ か、notarised のブロック以外への進捗のなさの
    証拠があるとき。 -/
theorem send_nullify (h : PreInv f i p)
    (hH : p.notarised = none ∨ ∃ c₀, p.notarised = some c₀ ∧ NoProgress f p.S p.view (some c₀))
    (j : Fin n) : PreInv f i (p.send i (Msg.nullify i p.view) j) := by
  have hV : ∀ c, Msg.vote i c ∈ (p.send i (Msg.nullify i p.view) j).S → Msg.vote i c ∈ p.S :=
    fun c hc => (mem_S_send_iff_of_ne i p j (by simp)).mp hc
  have hN : ∀ w, Msg.nullify i w ∈ (p.send i (Msg.nullify i p.view) j).S →
      w = p.view ∨ Msg.nullify i w ∈ p.S := by
    intro w hw
    rw [Processor.send_S] at hw
    split_ifs at hw
    · rcases Finset.mem_insert.mp hw with hw | hw
      · exact Or.inl (by cases hw; rfl)
      · exact Or.inr hw
    · exact Or.inr hw
  have hview := Processor.send_view i p (Msg.nullify i p.view) j
  have hnot := Processor.send_notarised_of_not_vote i p (Msg.nullify i p.view) j
    fun b hb => by cases hb
  have hnl := Processor.send_nullify_nullified i p p.view j
  rw [if_pos rfl] at hnl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hview]; exact h.view_pos
  · intro c hc; rw [hview, hnot]; exact h.notar c (hV c hc)
  · intro c c' hc hc'; exact h.unique c c' (hV c hc) (hV c' hc')
  · intro c hc; rw [hnot] at hc; rw [hview]; exact h.notar_view c hc
  · intro w hw
    rw [hview]
    rcases hN w hw with rfl | hw
    · exact ⟨h.view_pos, le_refl _⟩
    · exact h.null_view w hw
  · intro _; exact hnl
  · intro w c hw hc hcw
    have hc' := hV c hc
    rcases hN w hw with rfl | hw
    · obtain ⟨_, hlt | ⟨_, hcn⟩⟩ := h.notar c hc'
      · rw [hcw] at hlt; exact absurd hlt (lt_irrefl _)
      · rcases hH with hH | ⟨c₀, hc₀, hnp⟩
        · rw [hH] at hcn; cases hcn
        · rw [hc₀] at hcn
          rw [← Option.some.inj hcn]
          exact hnp.mono (Processor.S_subset_send i p _ j)
    · exact (h.null_vote w c hw hc' hcw).mono (Processor.S_subset_send i p _ j)

omit [DecidableEq Tx] in
/-- 次の view へ進んでも保たれる。 -/
theorem progress (h : PreInv f i p) : PreInv f i p.progress := by
  refine ⟨Nat.le_succ_of_le h.view_pos, ?_, fun c c' hc hc' hv => h.unique c c' hc hc' hv,
    ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨hpos, hlt | ⟨hce, _⟩⟩ := h.notar c hc
    · exact ⟨hpos, Or.inl (Nat.lt_succ_of_lt hlt)⟩
    · exact ⟨hpos, Or.inl (by simp only [Processor.progress]; rw [hce]; exact Nat.lt_succ_self _)⟩
  · intro c hc; simp [Processor.progress] at hc
  · intro w hw
    obtain ⟨h1, h2⟩ := h.null_view w hw
    exact ⟨h1, Nat.le_succ_of_le h2⟩
  · intro hw
    have := (h.null_view _ hw).2
    simp only [Processor.progress] at this
    omega
  · intro w c hw hc hcw; exact h.null_vote w c hw hc hcw

/-! #### 全員への送信 -/

theorem foldl_send_of_not_own (h : PreInv f i p) {m : Msg n Tx} (hv : ∀ b, m ≠ Msg.vote i b)
    (hn : ∀ v, m ≠ Msg.nullify i v) (l : List (Fin n)) :
    PreInv f i (l.foldl (fun p j => p.send i m j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih => exact ih (h.send_of_not_own hv hn j)

theorem foldl_send_of_mem_eq (h : PreInv f i p) {m : Msg n Tx} (hm : m ∈ p.S) (l : List (Fin n)) :
    PreInv f i (l.foldl (fun p j => p.send i m j) p)
      ∧ (l.foldl (fun p j => p.send i m j) p).notarised = p.notarised
      ∧ (l.foldl (fun p j => p.send i m j) p).nullified = p.nullified
      ∧ (l.foldl (fun p j => p.send i m j) p).S = p.S := by
  induction l generalizing p with
  | nil => exact ⟨h, rfl, rfl, rfl⟩
  | cons j l ih =>
    obtain ⟨hn, hnl, hS⟩ := h.send_of_mem_eq hm j
    obtain ⟨h', hn', hnl', hS'⟩ := ih (h.send_of_mem hm j) (hS ▸ hm)
    exact ⟨h', hn'.trans hn, hnl'.trans hnl, hS'.trans hS⟩

theorem foldl_send_nullified_of_not_nullify {m : Msg n Tx} (hn : ∀ v, m ≠ Msg.nullify i v)
    (l : List (Fin n)) (p : Processor n Tx) :
    (l.foldl (fun p j => p.send i m j) p).nullified = p.nullified := by
  induction l generalizing p with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons, ih,
      Processor.send_nullified_of_not_nullify i p m j fun v hv => absurd hv (hn v)]

theorem foldl_send_view (m : Msg n Tx) (l : List (Fin n)) (p : Processor n Tx) :
    (l.foldl (fun p j => p.send i m j) p).view = p.view := by
  induction l generalizing p with
  | nil => rfl
  | cons j l ih => rw [List.foldl_cons, ih, Processor.send_view]

theorem foldl_send_vote (h : PreInv f i p) {b : Block Tx} (hb : b.view = p.view)
    (hn : p.notarised = none ∨ p.notarised = some b) (hnn : Msg.nullify i p.view ∉ p.S)
    (l : List (Fin n)) : PreInv f i (l.foldl (fun p j => p.send i (Msg.vote i b) j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih =>
    refine ih (h.send_vote hb hn hnn j) (by rw [Processor.send_view]; exact hb) ?_ ?_
    · right; rw [Processor.send_vote_notarised, if_pos hb]
    · rw [Processor.send_view]
      exact fun hw => hnn ((mem_S_send_iff_of_ne i p j (by simp)).mp hw)

theorem foldl_send_vote_notarised {b : Block Tx} (hb : b.view = p.view) {l : List (Fin n)}
    (hl : l ≠ []) : (l.foldl (fun p j => p.send i (Msg.vote i b) j) p).notarised = some b := by
  induction l generalizing p with
  | nil => exact absurd rfl hl
  | cons j l ih =>
    rw [List.foldl_cons]
    rcases l with _ | ⟨j', l⟩
    · simp only [List.foldl_nil]; rw [Processor.send_vote_notarised, if_pos hb]
    · exact ih (by rw [Processor.send_view]; exact hb) (List.cons_ne_nil _ _)

theorem foldl_send_nullify (h : PreInv f i p) {v : View} (hv : v = p.view)
    (hH : p.notarised = none ∨ ∃ c₀, p.notarised = some c₀ ∧ NoProgress f p.S v (some c₀))
    (l : List (Fin n)) :
    PreInv f i (l.foldl (fun p j => p.send i (Msg.nullify i v) j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih =>
    subst hv
    rw [List.foldl_cons]
    refine ih (h.send_nullify hH j) (Processor.send_view i p _ j).symm ?_
    rw [Processor.send_notarised_of_not_vote i p _ j fun b hb => by cases hb]
    exact hH.imp_right fun ⟨c₀, hc₀, hnp⟩ =>
      ⟨c₀, hc₀, hnp.mono (Processor.S_subset_send i p _ j)⟩

theorem foldl_send_notarised_of_not_vote {m : Msg n Tx} (hv : ∀ b, m ≠ Msg.vote i b)
    (l : List (Fin n)) (p : Processor n Tx) :
    (l.foldl (fun p j => p.send i m j) p).notarised = p.notarised := by
  induction l generalizing p with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons, ih, Processor.send_notarised_of_not_vote i p m j fun b hb => absurd hb (hv b)]

end PreInv

namespace LocalInv

variable {f : Nat} {i : Fin n} {p : Processor n Tx}

omit [DecidableEq Tx] in
theorem of_grow (h : LocalInv f i p) {q : Processor n Tx} (hv : q.view = p.view)
    (hn : q.notarised = p.notarised) (hnl : q.nullified = p.nullified) (hS : p.S ⊆ q.S)
    (hvote : ∀ c, Msg.vote i c ∈ q.S → Msg.vote i c ∈ p.S)
    (hnull : ∀ w, Msg.nullify i w ∈ q.S → Msg.nullify i w ∈ p.S) : LocalInv f i q :=
  ⟨h.toPreInv.of_grow hv hn hnl hS hvote hnull, fun c hc => hS (h.notar_mem c (hn ▸ hc)),
   fun hq => by rw [hv]; exact hS (h.null_mem (hnl ▸ hq))⟩

omit [DecidableEq Tx] in
theorem of_sgrows (h : LocalInv f i p) {q : Processor n Tx} (hg : p.SGrows q)
    (hvote : ∀ c, Msg.vote i c ∈ q.S → Msg.vote i c ∈ p.S)
    (hnull : ∀ w, Msg.nullify i w ∈ q.S → Msg.nullify i w ∈ p.S) : LocalInv f i q :=
  h.of_grow hg.view hg.notarised hg.nullified hg.S hvote hnull

omit [DecidableEq Tx] in
theorem tick (h : LocalInv f i p) (S₀ : Finset (Msg n Tx)) : LocalInv f i (p.tick S₀) :=
  h.of_grow rfl rfl rfl (Finset.Subset.refl _) (fun _ hc => hc) (fun _ hw => hw)

omit [DecidableEq Tx] in
theorem progress (h : LocalInv f i p) : LocalInv f i p.progress :=
  ⟨h.toPreInv.progress, fun c hc => by simp [Processor.progress] at hc,
   fun hq => by simp [Processor.progress] at hq⟩

theorem disseminate_of_not_own (h : LocalInv f i p) {m : Msg n Tx} (hv : ∀ b, m ≠ Msg.vote i b)
    (hn : ∀ v, m ≠ Msg.nullify i v) : LocalInv f i (disseminate i p m).1 := by
  rw [disseminate_fst]
  refine ⟨h.toPreInv.foldl_send_of_not_own hv hn _, fun c hc => ?_, fun hq => ?_⟩
  · rw [PreInv.foldl_send_notarised_of_not_vote hv] at hc
    exact S_subset_foldl_send i m _ p (h.notar_mem c hc)
  · rw [PreInv.foldl_send_nullified_of_not_nullify hn] at hq
    rw [PreInv.foldl_send_view]
    exact S_subset_foldl_send i m _ p (h.null_mem hq)

theorem disseminate_of_mem (h : LocalInv f i p) {m : Msg n Tx} (hm : m ∈ p.S) :
    LocalInv f i (disseminate i p m).1 := by
  rw [disseminate_fst]
  obtain ⟨h', hn, hnl, hS⟩ := h.toPreInv.foldl_send_of_mem_eq hm (List.finRange n)
  exact ⟨h', fun c hc => by rw [hS]; exact h.notar_mem c (hn ▸ hc),
    fun hq => by rw [hS, PreInv.foldl_send_view]; exact h.null_mem (hnl ▸ hq)⟩

theorem disseminate_vote (h : LocalInv f i p) {b : Block Tx} (hb : b.view = p.view)
    (hn : p.notarised = none ∨ p.notarised = some b) (hnn : Msg.nullify i p.view ∉ p.S) :
    LocalInv f i (disseminate i p (Msg.vote i b)).1 := by
  have hmem := mem_S_disseminate_fst i p (Msg.vote i b)
  rw [disseminate_fst] at hmem ⊢
  refine ⟨h.toPreInv.foldl_send_vote hb hn hnn _, fun c hc => ?_, fun hq => ?_⟩
  · rw [PreInv.foldl_send_vote_notarised hb (List.ne_nil_of_mem (List.mem_finRange i))] at hc
    rw [← Option.some.inj hc]
    exact hmem
  · rw [PreInv.foldl_send_nullified_of_not_nullify (fun v hv => by cases hv)] at hq
    rw [PreInv.foldl_send_view]
    exact S_subset_foldl_send i _ _ p (h.null_mem hq)

theorem disseminate_nullify (h : LocalInv f i p)
    (hH : p.notarised = none ∨ ∃ c₀, p.notarised = some c₀ ∧ NoProgress f p.S p.view (some c₀)) :
    LocalInv f i (disseminate i p (Msg.nullify i p.view)).1 := by
  have hmem := mem_S_disseminate_fst i p (Msg.nullify i p.view)
  rw [disseminate_fst] at hmem ⊢
  refine ⟨h.toPreInv.foldl_send_nullify rfl hH _, fun c hc => ?_, fun _ => ?_⟩
  · rw [PreInv.foldl_send_notarised_of_not_vote (fun b hb => by cases hb)] at hc
    exact S_subset_foldl_send i _ _ p (h.notar_mem c hc)
  · rw [PreInv.foldl_send_view]; exact hmem

theorem disseminateAll_of_mem (h : LocalInv f i p) {ms : List (Msg n Tx)} (hm : ∀ m ∈ ms, m ∈ p.S) :
    LocalInv f i (disseminateAll i p ms).1 := by
  rw [disseminateAll_fst]
  induction ms generalizing p with
  | nil => exact h
  | cons m ms ih =>
    exact ih (h.disseminate_of_mem (hm m (List.mem_cons_self ..))) fun m' hm' =>
      S_subset_disseminate_fst i p m (hm m' (List.mem_cons_of_mem _ hm'))

/-! #### 各段 -/

theorem forwardNew (h : LocalInv f i p) : LocalInv f i (forwardNew f i p).1 := by
  rw [forwardNew_eq]
  exact h.disseminateAll_of_mem fun m hm => mem_S_of_mem_forwardMsgs hm

theorem propose (h : LocalInv f i p) (lead : View → Fin n) :
    LocalInv f i (propose f lead i p).1 := by
  unfold Algo.propose
  split_ifs
  · exact h.disseminate_of_not_own (fun _ h => by cases h) (fun _ h => by cases h)
  · exact h

theorem voteProposal (h : LocalInv f i p) (lead : View → Fin n) :
    LocalInv f i (voteProposal f lead i p).1 := by
  unfold Algo.voteProposal
  rcases proposals lead p.S p.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · exact h
  · simp only
    split_ifs with hg
    · refine h.disseminate_vote hg.1.view (Or.inl hg.2.1) fun hw => ?_
      have := h.null_flag hw
      rw [hg.2.2] at this
      cases this
    · exact h
  · exact h

theorem nullifyTimeout (h : LocalInv f i p) (Δ : Nat) : LocalInv f i (nullifyTimeout Δ i p).1 := by
  unfold Algo.nullifyTimeout
  split_ifs with hg
  · exact h.disseminate_nullify (Or.inl hg.2.2)
  · exact h

theorem advanceNull (h : LocalInv f i p) : LocalInv f i (advanceNull f p).1 := by
  unfold Algo.advanceNull
  split_ifs
  · exact h.progress
  · exact h

theorem advanceM (h : LocalInv f i p) : LocalInv f i (advanceM f i p).1 := by
  unfold Algo.advanceM
  rcases hm : mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · exact h
  · simp only
    split_ifs with hg
    · refine (h.disseminate_vote (mem_mNotarisedAt (hm ▸ List.mem_cons_self ..)).1
        (Or.inl hg.1) fun hw => ?_).progress
      have := h.null_flag hw
      rw [hg.2] at this
      cases this
    · exact h.progress

theorem nullifyNoProgress (h : LocalInv f i p) : LocalInv f i (nullifyNoProgress f i p).1 := by
  unfold Algo.nullifyNoProgress
  split_ifs with hg
  · obtain ⟨c₀, hc₀⟩ := Option.ne_none_iff_exists'.mp hg.2.1
    refine h.disseminate_nullify (Or.inr ⟨c₀, hc₀, ?_⟩)
    rw [← hc₀]; exact hg.2.2
  · exact h

/-- Algorithm 1 の 1 スロット分の動作は不変量を保つ。 -/
theorem stepPair (h : LocalInv f i p) (Δ : Nat) (lead : View → Fin n) :
    LocalInv f i (stepPair f Δ lead i p).1 :=
  ((((((h.forwardNew.propose lead).voteProposal lead).nullifyTimeout Δ).advanceNull
    ).advanceM).nullifyNoProgress)

end LocalInv


/-! ### 段ごとの入力状態と、送信の出所 -/

section Stages

variable (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx)

/-- 各段の入力となる局所状態。st1 は 2〜3 行の後、st2 は 5〜7 行の後、…、st6 は 19〜21 行の後。 -/
noncomputable def st1 : Processor n Tx := (forwardNew f i p).1
noncomputable def st2 : Processor n Tx := (propose f lead i (st1 f i p)).1
noncomputable def st3 : Processor n Tx := (voteProposal f lead i (st2 f lead i p)).1
noncomputable def st4 : Processor n Tx := (nullifyTimeout Δ i (st3 f lead i p)).1
noncomputable def st5 : Processor n Tx := (advanceNull f (st4 f Δ lead i p)).1
noncomputable def st6 : Processor n Tx := (advanceM f i (st5 f Δ lead i p)).1

theorem stepPair_snd : (stepPair f Δ lead i p).2 =
    (forwardNew f i p).2 ++ (propose f lead i (st1 f i p)).2
      ++ (voteProposal f lead i (st2 f lead i p)).2 ++ (nullifyTimeout Δ i (st3 f lead i p)).2
      ++ (advanceNull f (st4 f Δ lead i p)).2 ++ (advanceM f i (st5 f Δ lead i p)).2
      ++ (nullifyNoProgress f i (st6 f Δ lead i p)).2 := rfl

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

theorem advanceNull_eq (f : Nat) (p : Processor n Tx) :
    (advanceNull f p).1 = p ∨ (advanceNull f p).1 = p.progress := by
  unfold advanceNull; split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem advanceNull_eq_of_view (f : Nat) (p : Processor n Tx)
    (h : (advanceNull f p).1.view = p.view) : (advanceNull f p).1 = p := by
  rcases advanceNull_eq f p with h' | h'
  · exact h'
  · exfalso
    rw [h'] at h
    have := congrArg View.val h
    simp [Processor.progress] at this

theorem advanceM_view (f : Nat) (i : Fin n) (p : Processor n Tx) :
    (advanceM f i p).1.view = p.view ∨ (advanceM f i p).1.view.val = p.view.val + 1 := by
  unfold advanceM
  rcases mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · exact Or.inl rfl
  · simp only
    split_ifs
    · right; simp [Processor.progress, disseminate_view]
    · right; simp [Processor.progress]

theorem st3_view (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st3 f lead i p).view = p.view := by
  simp only [st3, st2, st1, voteProposal_view, propose_view, forwardNew_view]

theorem st4_view (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st4 f Δ lead i p).view = p.view := by
  simp only [st4, nullifyTimeout_view, st3_view]

/-- 段を進めても S は減らない。 -/
theorem S_subset_st3 (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (st3 f lead i p).S :=
  (S_subset_forwardNew f i p).trans ((S_subset_propose f lead i _).trans
    (S_subset_voteProposal f lead i _))

theorem S_subset_st6 (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (st6 f Δ lead i p).S :=
  (S_subset_st3 f lead i p).trans ((S_subset_nullifyTimeout Δ i _).trans
    ((S_subset_advanceNull f _).trans (S_subset_advanceM f i _)))

theorem S_st3_subset_st6 (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st3 f lead i p).S ⊆ (st6 f Δ lead i p).S :=
  (S_subset_nullifyTimeout Δ i _).trans
    ((S_subset_advanceNull f _).trans (S_subset_advanceM f i _))

/-! #### 各段の後の S にある message は、前からあったか自分の署名付き -/

theorem mem_S_send_or_signer (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n)
    {m' : Msg n Tx} (h : m' ∈ (p.send i m j).S) : m' ∈ p.S ∨ m' = m := by
  rw [Processor.send_S] at h
  split_ifs at h
  · exact (Finset.mem_insert.mp h).symm.imp_left id
  · exact Or.inl h

theorem mem_S_disseminate_or (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) {m' : Msg n Tx}
    (h : m' ∈ (disseminate i p m).1.S) : m' ∈ p.S ∨ m' = m := by
  rw [disseminate_fst] at h
  generalize List.finRange n = l at h
  induction l generalizing p with
  | nil => exact Or.inl h
  | cons j l ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h | h
    · exact mem_S_send_or_signer i p m j h
    · exact Or.inr h

theorem mem_S_stage_or (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx)
    {m : Msg n Tx} (h : m ∈ (st6 f Δ lead i p).S) : m ∈ p.S ∨ m.signer = some i := by
  -- 各段で、S に入る message は前からあったか、自分の署名付き
  have h1 : ∀ q : Processor n Tx, ∀ m ∈ (forwardNew f i q).1.S, m ∈ q.S := by
    intro q m hm
    rw [forwardNew_eq, disseminateAll_fst] at hm
    have key : ∀ (ms : List (Msg n Tx)) (q : Processor n Tx), (∀ m ∈ ms, m ∈ q.S) →
        ∀ m ∈ (ms.foldl (fun p m => (disseminate i p m).1) q).S, m ∈ q.S := by
      intro ms
      induction ms with
      | nil => intro q _ m hm; exact hm
      | cons m' ms ih =>
        intro q hq m hm
        rw [List.foldl_cons] at hm
        have hm' := ih _ (fun m'' hm'' => S_subset_disseminate_fst i q m'
          (hq m'' (List.mem_cons_of_mem _ hm''))) m hm
        rcases mem_S_disseminate_or i q m' hm' with h | rfl
        · exact h
        · exact hq m (List.mem_cons_self ..)
    exact key _ q (fun m hm => mem_S_of_mem_forwardMsgs hm) m hm
  have h2 : ∀ q : Processor n Tx, ∀ m ∈ (propose f lead i q).1.S, m ∈ q.S ∨ m.signer = some i := by
    intro q m hm
    unfold propose at hm
    split_ifs at hm
    · exact (mem_S_disseminate_or i q _ hm).imp_right fun h => by rw [h]; rfl
    · exact Or.inl hm
  have h3 : ∀ q : Processor n Tx, ∀ m ∈ (voteProposal f lead i q).1.S,
      m ∈ q.S ∨ m.signer = some i := by
    intro q m hm
    unfold voteProposal at hm
    generalize proposals lead q.S q.view = l at hm
    rcases l with _ | ⟨b, _ | ⟨b', l⟩⟩
    · exact Or.inl hm
    · simp only at hm
      split_ifs at hm
      · exact (mem_S_disseminate_or i q _ hm).imp_right fun h => by rw [h]; rfl
      · exact Or.inl hm
    · exact Or.inl hm
  have h4 : ∀ q : Processor n Tx, ∀ m ∈ (nullifyTimeout Δ i q).1.S, m ∈ q.S ∨ m.signer = some i := by
    intro q m hm
    unfold nullifyTimeout at hm
    split_ifs at hm
    · exact (mem_S_disseminate_or i q _ hm).imp_right fun h => by rw [h]; rfl
    · exact Or.inl hm
  have h5 : ∀ q : Processor n Tx, ∀ m ∈ (advanceNull f q).1.S, m ∈ q.S := by
    intro q m hm
    rcases advanceNull_eq f q with h | h <;> rw [h] at hm <;> exact hm
  have h6 : ∀ q : Processor n Tx, ∀ m ∈ (advanceM f i q).1.S, m ∈ q.S ∨ m.signer = some i := by
    intro q m hm
    unfold advanceM at hm
    generalize mNotarisedAt f q.S q.view = l at hm
    rcases l with _ | ⟨b, l⟩
    · exact Or.inl hm
    · simp only at hm
      split_ifs at hm
      · exact (mem_S_disseminate_or i q _ hm).imp_right fun h => by rw [h]; rfl
      · exact Or.inl hm
  simp only [st6, st5, st4, st3, st2, st1] at h
  rcases h6 _ _ h with h | h
  · rcases h4 _ _ (h5 _ _ h) with h | h
    · rcases h3 _ _ h with h | h
      · rcases h2 _ _ h with h | h
        · exact Or.inl (h1 _ _ h)
        · exact Or.inr h
      · exact Or.inr h
    · exact Or.inr h
  · exact Or.inr h

/-! #### 各段の後の S の中身 -/

theorem mem_S_forwardNew {f : Nat} {i : Fin n} {q : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (forwardNew f i q).1.S) : m ∈ q.S := by
  rw [forwardNew_eq, disseminateAll_fst] at hm
  have key : ∀ (ms : List (Msg n Tx)) (q : Processor n Tx), (∀ m ∈ ms, m ∈ q.S) →
      ∀ m ∈ (ms.foldl (fun p m => (disseminate i p m).1) q).S, m ∈ q.S := by
    intro ms
    induction ms with
    | nil => intro q _ m hm; exact hm
    | cons m' ms ih =>
      intro q hq m hm
      rw [List.foldl_cons] at hm
      have hm' := ih _ (fun m'' hm'' => S_subset_disseminate_fst i q m'
        (hq m'' (List.mem_cons_of_mem _ hm''))) m hm
      rcases mem_S_disseminate_or i q m' hm' with h | rfl
      · exact h
      · exact hq m (List.mem_cons_self ..)
  exact key _ q (fun m hm => mem_S_of_mem_forwardMsgs hm) m hm

theorem mem_S_propose {f : Nat} {lead : View → Fin n} {i : Fin n} {q : Processor n Tx}
    {m : Msg n Tx} (hm : m ∈ (propose f lead i q).1.S) : m ∈ q.S ∨ ∃ b, m = Msg.block i b := by
  unfold propose at hm
  split_ifs at hm
  · exact (mem_S_disseminate_or i q _ hm).imp_right fun h => ⟨_, h⟩
  · exact Or.inl hm

theorem mem_S_voteProposal {f : Nat} {lead : View → Fin n} {i : Fin n} {q : Processor n Tx}
    {m : Msg n Tx} (hm : m ∈ (voteProposal f lead i q).1.S) :
    m ∈ q.S ∨ ∃ b, m = Msg.vote i b ∧ Action.send (Msg.vote i b) i ∈ (voteProposal f lead i q).2 := by
  unfold voteProposal at hm ⊢
  generalize proposals lead q.S q.view = l at hm ⊢
  rcases l with _ | ⟨b, _ | ⟨b', l⟩⟩
  · exact Or.inl hm
  · simp only at hm ⊢
    split_ifs at hm ⊢
    · exact (mem_S_disseminate_or i q _ hm).imp_right fun h => ⟨b, h, mem_disseminate_snd.mpr ⟨i, rfl⟩⟩
    · exact Or.inl hm
  · exact Or.inl hm

theorem mem_S_nullifyTimeout {Δ : Nat} {i : Fin n} {q : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (nullifyTimeout Δ i q).1.S) : m ∈ q.S ∨ ∃ v, m = Msg.nullify i v := by
  unfold nullifyTimeout at hm
  split_ifs at hm
  · exact (mem_S_disseminate_or i q _ hm).imp_right fun h => ⟨_, h⟩
  · exact Or.inl hm

theorem mem_S_advanceNull {f : Nat} {q : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (advanceNull f q).1.S) : m ∈ q.S := by
  rcases advanceNull_eq f q with h | h <;> rw [h] at hm <;> exact hm

theorem mem_S_st2 {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (st2 f lead i p).S) : m ∈ p.S ∨ ∃ b, m = Msg.block i b :=
  (mem_S_propose hm).imp_left mem_S_forwardNew

theorem mem_S_st3 {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (st3 f lead i p).S) :
    m ∈ (st2 f lead i p).S
      ∨ ∃ b, m = Msg.vote i b ∧ Action.send (Msg.vote i b) i ∈ (voteProposal f lead i (st2 f lead i p)).2 :=
  mem_S_voteProposal hm

theorem mem_S_st5 {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (st5 f Δ lead i p).S) : m ∈ (st3 f lead i p).S ∨ ∃ v, m = Msg.nullify i v :=
  mem_S_nullifyTimeout (mem_S_advanceNull hm)

/-! #### 各段が送る message とそのときの条件 -/

theorem send_forwardNew_mem {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (forwardNew f i p).2) : m ∈ p.S := by
  rw [forwardNew_eq] at h
  obtain ⟨m', hm', _, hm⟩ := mem_disseminateAll_snd.mp h
  cases hm
  exact mem_S_of_mem_forwardMsgs hm'

theorem send_propose_eq {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    {m : Msg n Tx} {j : Fin n} (h : Action.send m j ∈ (propose f lead i p).2) :
    ∃ b, m = Msg.block i b := by
  unfold propose at h
  split_ifs at h
  · obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
    cases hm; exact ⟨_, rfl⟩
  · simp at h

theorem send_voteProposal_eq {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    {m : Msg n Tx} {j : Fin n} (h : Action.send m j ∈ (voteProposal f lead i p).2) :
    ∃ b, m = Msg.vote i b ∧ b.view = p.view ∧ p.notarised = none ∧ p.nullified = false
      ∧ ValidProposal f lead p.S p.view b ∧ (voteProposal f lead i p).1.notarised = some b := by
  unfold voteProposal at h ⊢
  generalize proposals lead p.S p.view = l at h ⊢
  rcases l with _ | ⟨b, _ | ⟨b', l⟩⟩
  · simp at h
  · simp only at h ⊢
    split_ifs at h ⊢ with hg
    · obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
      cases hm
      refine ⟨b, rfl, hg.1.view, hg.2.1, hg.2.2, hg.1, ?_⟩
      rw [disseminate_fst]
      exact PreInv.foldl_send_vote_notarised hg.1.view (List.ne_nil_of_mem (List.mem_finRange i))
    · simp at h
  · simp at h

theorem send_nullifyTimeout_eq {Δ : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (nullifyTimeout Δ i p).2) :
    m = Msg.nullify i p.view ∧ p.nullified = false ∧ p.notarised = none
      ∧ (nullifyTimeout Δ i p).1.nullified = true := by
  unfold nullifyTimeout at h ⊢
  split_ifs at h ⊢ with hg
  · obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
    cases hm
    refine ⟨rfl, hg.2.1, hg.2.2, ?_⟩
    rw [disseminate_fst]
    have key : ∀ (l : List (Fin n)) (q : Processor n Tx), l ≠ [] → q.view = p.view →
        (l.foldl (fun q j => q.send i (Msg.nullify i p.view) j) q).nullified = true := by
      intro l
      induction l with
      | nil => intro _ h; exact absurd rfl h
      | cons j l ih =>
        intro q _ hq
        rw [List.foldl_cons]
        rcases l with _ | ⟨j', l⟩
        · simp only [List.foldl_nil]
          rw [Processor.send_nullify_nullified, if_pos hq.symm]
        · exact ih _ (List.cons_ne_nil _ _) (by rw [Processor.send_view]; exact hq)
    exact key _ p (List.ne_nil_of_mem (List.mem_finRange i)) rfl
  · simp at h

theorem send_advanceNull {f : Nat} {p : Processor n Tx} {m : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (advanceNull f p).2) : False := by
  unfold advanceNull at h
  split_ifs at h <;> simp at h

theorem send_advanceM_eq {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (advanceM f i p).2) :
    ∃ b, m = Msg.vote i b ∧ b.view = p.view ∧ MNotarised f p.S b ∧ p.notarised = none
      ∧ p.nullified = false ∧ (advanceM f i p).1.view.val = p.view.val + 1 := by
  unfold advanceM at h ⊢
  generalize hl : mNotarisedAt f p.S p.view = l at h ⊢
  rcases l with _ | ⟨b, l⟩
  · simp at h
  · simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h
    simp only
    split_ifs at h ⊢ with hg
    · obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
      cases hm
      have hb := mem_mNotarisedAt (hl ▸ List.mem_cons_self ..)
      exact ⟨b, rfl, hb.1, hb.2, hg.1, hg.2, by simp [Processor.progress, disseminate_view]⟩
    · simp at h

theorem send_nullifyNoProgress_eq {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (nullifyNoProgress f i p).2) :
    m = Msg.nullify i p.view ∧ p.nullified = false
      ∧ ∃ c₀, p.notarised = some c₀ ∧ NoProgress f p.S p.view (some c₀) := by
  unfold nullifyNoProgress at h
  split_ifs at h with hg
  · obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
    cases hm
    obtain ⟨c₀, hc₀⟩ := Option.ne_none_iff_exists'.mp hg.2.1
    exact ⟨rfl, hg.1, c₀, hc₀, by rw [← hc₀]; exact hg.2.2⟩
  · simp at h

/-! #### 票と nullify の出所 -/

theorem localInv_st3 {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) : LocalInv f i (st3 f lead i p) :=
  (h.forwardNew.propose lead).voteProposal lead

theorem localInv_st6 {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) : LocalInv f i (st6 f Δ lead i p) :=
  ((localInv_st3 (lead := lead) h).nullifyTimeout Δ).advanceNull.advanceM

/-- 自分の票の出所: S にあった（転送）か、9〜11 行か 19〜21 行で、その段の入力 q は現在の
    view が b の view で、notarised = ⊥、nullified = false、S に valid proposal か
    M-notarisation がある。 -/
theorem vote_emission {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) {b : Block Tx} {j : Fin n}
    (hv : Action.send (Msg.vote i b) j ∈ Algo.step f Δ lead i p) :
    Msg.vote i b ∈ p.S ∨ ∃ q : Processor n Tx, LocalInv f i q ∧ q.view = b.view
      ∧ q.notarised = none ∧ q.nullified = false ∧ p.S ⊆ q.S
      ∧ (∀ m ∈ q.S, m ∈ p.S ∨ m.signer = some i)
      ∧ (ValidProposal f lead q.S q.view b ∨ MNotarised f q.S b) := by
  have hst6 : ∀ m ∈ (st6 f Δ lead i p).S, m ∈ p.S ∨ m.signer = some i :=
    fun m hm => mem_S_stage_or f Δ lead i p hm
  rw [step_eq_stepPair, stepPair_snd] at hv
  simp only [List.mem_append] at hv
  rcases hv with ((((((hv | hv) | hv) | hv) | hv) | hv) | hv)
  · exact Or.inl (send_forwardNew_mem hv)
  · obtain ⟨_, hm⟩ := send_propose_eq hv; cases hm
  · obtain ⟨b', hm, hbv, hnot, hnl, hvp, _⟩ := send_voteProposal_eq hv
    injection hm with _ hbb
    subst hbb
    refine Or.inr ⟨st2 f lead i p, h.forwardNew.propose lead, hbv.symm, hnot, hnl, ?_, ?_,
      Or.inl hvp⟩
    · exact (S_subset_forwardNew f i p).trans (S_subset_propose f lead i _)
    · intro m hm
      exact hst6 m ((S_subset_voteProposal f lead i _).trans (S_st3_subset_st6 f Δ lead i p) hm)
  · obtain ⟨hm, _⟩ := send_nullifyTimeout_eq hv; cases hm
  · exact absurd hv send_advanceNull
  · obtain ⟨b', hm, hbv, hM, hnot, hnl, _⟩ := send_advanceM_eq hv
    injection hm with _ hbb
    subst hbb
    refine Or.inr ⟨st5 f Δ lead i p, ((localInv_st3 (lead := lead) h).nullifyTimeout Δ).advanceNull,
      hbv.symm, hnot, hnl, ?_, ?_, Or.inr hM⟩
    · exact (S_subset_st3 f lead i p).trans ((S_subset_nullifyTimeout Δ i _).trans
        (S_subset_advanceNull f _))
    · intro m hm
      exact hst6 m (S_subset_advanceM f i _ hm)
  · obtain ⟨hm, _⟩ := send_nullifyNoProgress_eq hv; cases hm

/-- 自分の nullify(b.view) を出し、b への自分の票が S にあるか同じスロットで出すなら、
    nullify は 24〜28 行で、その段の入力 st6 には b 以外への進捗のなさの証拠がある。 -/
theorem nullify_after_vote {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) {b : Block Tx} {j j' : Fin n}
    (hb : Msg.vote i b ∈ p.S ∨ Action.send (Msg.vote i b) j ∈ Algo.step f Δ lead i p)
    (hn : Action.send (Msg.nullify i b.view) j' ∈ Algo.step f Δ lead i p)
    (hno : Msg.nullify i b.view ∉ p.S) :
    LocalInv f i (st6 f Δ lead i p) ∧ (st6 f Δ lead i p).view = b.view
      ∧ (st6 f Δ lead i p).nullified = false ∧ Msg.vote i b ∈ (st6 f Δ lead i p).S
      ∧ NoProgress f (st6 f Δ lead i p).S b.view (some b) := by
  have h3 : LocalInv f i (st3 f lead i p) := localInv_st3 h
  have h6 : LocalInv f i (st6 f Δ lead i p) := localInv_st6 h
  -- 票の出所（同じスロットで出す場合）を先に整理する
  have hvote : Msg.vote i b ∈ p.S
      ∨ (Msg.vote i b ∈ (st3 f lead i p).S ∧ (st3 f lead i p).notarised = some b)
      ∨ (b.view = (st5 f Δ lead i p).view ∧ (st5 f Δ lead i p).nullified = false
          ∧ (st6 f Δ lead i p).view.val = (st5 f Δ lead i p).view.val + 1) := by
    rcases hb with hb | hb
    · exact Or.inl hb
    · rw [step_eq_stepPair, stepPair_snd] at hb
      simp only [List.mem_append] at hb
      rcases hb with ((((((hb | hb) | hb) | hb) | hb) | hb) | hb)
      · exact Or.inl (send_forwardNew_mem hb)
      · obtain ⟨_, hm⟩ := send_propose_eq hb; cases hm
      · obtain ⟨b', hm, _, _, _, _, hnot⟩ := send_voteProposal_eq hb
        injection hm with _ hbb
        subst hbb
        exact Or.inr (Or.inl ⟨mem_S_of_send_voteProposal hb, hnot⟩)
      · obtain ⟨hm, _⟩ := send_nullifyTimeout_eq hb; cases hm
      · exact absurd hb send_advanceNull
      · obtain ⟨b', hm, hbv, _, _, hnl, hv6⟩ := send_advanceM_eq hb
        injection hm with _ hbb
        subst hbb
        exact Or.inr (Or.inr ⟨hbv, hnl, hv6⟩)
      · obtain ⟨hm, _⟩ := send_nullifyNoProgress_eq hb; cases hm
  rw [step_eq_stepPair, stepPair_snd] at hn
  simp only [List.mem_append] at hn
  rcases hn with ((((((hn | hn) | hn) | hn) | hn) | hn) | hn)
  · exact absurd (send_forwardNew_mem hn) hno
  · obtain ⟨_, hm⟩ := send_propose_eq hn; cases hm
  · obtain ⟨_, hm, _⟩ := send_voteProposal_eq hn; cases hm
  · -- 13〜14 行: st3 で notarised = ⊥ だが、b への票が st3 の S にあるか、同時に出せない
    exfalso
    obtain ⟨hm, hnl3, hnot3, hnl4⟩ := send_nullifyTimeout_eq hn
    injection hm with _ hv3
    rcases hvote with hb | ⟨hb, hnot⟩ | ⟨hbv5, hnl5, _⟩
    · have := ((h3.notar b (S_subset_st3 f lead i p hb)).2.resolve_left
        (by rw [hv3]; exact lt_irrefl _)).2
      rw [hnot3] at this; cases this
    · rw [hnot3] at hnot; cases hnot
    · have h45 : (advanceNull f (st4 f Δ lead i p)).1.view = (st4 f Δ lead i p).view := by
        change (st5 f Δ lead i p).view = _
        rw [← hbv5, hv3, st4_view, st3_view]
      have h5eq : st5 f Δ lead i p = st4 f Δ lead i p := advanceNull_eq_of_view f _ h45
      rw [h5eq] at hnl5
      change (nullifyTimeout Δ i (st3 f lead i p)).1.nullified = false at hnl5
      rw [hnl4] at hnl5; cases hnl5
  · exact absurd hn send_advanceNull
  · obtain ⟨_, hm, _⟩ := send_advanceM_eq hn; cases hm
  · -- 24〜28 行
    obtain ⟨hm, hnl6, c₀, hc₀, hnp⟩ := send_nullifyNoProgress_eq hn
    injection hm with _ hv6
    have hvote6 : Msg.vote i b ∈ (st6 f Δ lead i p).S := by
      rcases hvote with hb | ⟨hb, _⟩ | ⟨hbv5, _, hv6'⟩
      · exact S_subset_st6 f Δ lead i p hb
      · exact S_st3_subset_st6 f Δ lead i p hb
      · exfalso
        have : b.view.val = (st5 f Δ lead i p).view.val := by rw [hbv5]
        rw [hv6] at this
        omega
    have hnot6 := ((h6.notar b hvote6).2.resolve_left (by rw [hv6]; exact lt_irrefl _)).2
    rw [hc₀] at hnot6
    obtain rfl := Option.some.inj hnot6
    refine ⟨h6, hv6.symm, hnl6, hvote6, ?_⟩
    rw [hv6]; exact hnp

/-! #### 転送と反応のための補題 -/

omit [DecidableEq Tx] in
theorem mem_nullifyViews {S : Finset (Msg n Tx)} {q : Fin n} {v : View} (h : Msg.nullify q v ∈ S) :
    v ∈ nullifyViews S := by
  simp only [nullifyViews, List.mem_dedup, List.mem_filterMap, Finset.mem_toList]
  exact ⟨Msg.nullify q v, h, rfl⟩

theorem mem_votedBlocks {S : Finset (Msg n Tx)} {q : Fin n} {b : Block Tx} (h : Msg.vote q b ∈ S) :
    b ∈ votedBlocks S := by
  simp only [votedBlocks, List.mem_dedup, List.mem_filterMap, Finset.mem_toList]
  exact ⟨Msg.vote q b, h, rfl⟩

/-- 新しい nullification を構成する nullify は転送される。 -/
theorem mem_forwardMsgs_nullify {f : Nat} {p : Processor n Tx} {q : Fin n} {v : View}
    (h1 : Nullified f p.S v) (h2 : ¬ Nullified f p.prevS v) (hm : Msg.nullify q v ∈ p.S) :
    Msg.nullify q v ∈ forwardMsgs f p := by
  simp only [forwardMsgs, List.mem_append]
  left; left
  simp only [List.mem_flatMap, List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
  exact ⟨v, ⟨mem_nullifyViews hm, h1, h2⟩, hm, q, rfl⟩

/-- 新しい M-notarisation を構成する票は転送される。 -/
theorem mem_forwardMsgs_vote {f : Nat} {p : Processor n Tx} {q : Fin n} {b : Block Tx}
    (h1 : MNotarised f p.S b) (h2 : ¬ MNotarised f p.prevS b) (hm : Msg.vote q b ∈ p.S) :
    Msg.vote q b ∈ forwardMsgs f p := by
  simp only [forwardMsgs, List.mem_append]
  left; right
  simp only [List.mem_flatMap, List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
  exact ⟨b, ⟨mem_votedBlocks hm, h1, h2⟩, hm, q, rfl⟩

theorem send_mem_step_of_mem_forwardMsgs {f Δ : Nat} {lead : View → Fin n} {i : Fin n}
    {p : Processor n Tx} {m : Msg n Tx} (h : m ∈ forwardMsgs f p) (j : Fin n) :
    Action.send m j ∈ Algo.step f Δ lead i p := by
  rw [step_eq_stepPair, stepPair_snd]
  simp only [List.mem_append]
  left; left; left; left; left; left
  rw [forwardNew_eq]
  exact mem_disseminateAll_snd.mpr ⟨m, h, j, rfl⟩

/-- timer は送信で変わらない。 -/
theorem disseminate_timer (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    (disseminate i p m).1.timer = p.timer := by
  rw [disseminate_fst]
  generalize List.finRange n = l
  induction l generalizing p with
  | nil => rfl
  | cons j l ih => rw [List.foldl_cons, ih, Processor.send_timer]

theorem disseminateAll_timer (i : Fin n) (p : Processor n Tx) (ms : List (Msg n Tx)) :
    (disseminateAll i p ms).1.timer = p.timer := by
  rw [disseminateAll_fst]
  induction ms generalizing p with
  | nil => rfl
  | cons m ms ih => rw [List.foldl_cons, ih, disseminate_timer]

theorem st3_timer (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st3 f lead i p).timer = p.timer := by
  have h1 : (st1 f i p).timer = p.timer := by
    simp only [st1]; rw [forwardNew_eq]; exact disseminateAll_timer i p _
  have h2 : (st2 f lead i p).timer = (st1 f i p).timer := by
    simp only [st2]; unfold propose; split_ifs
    · exact disseminate_timer i _ _
    · rfl
  have h3 : (st3 f lead i p).timer = (st2 f lead i p).timer := by
    simp only [st3]; unfold voteProposal
    rcases proposals lead (st2 f lead i p).S (st2 f lead i p).view with _ | ⟨b, _ | ⟨b', l⟩⟩
    · rfl
    · simp only; split_ifs
      · exact disseminate_timer i _ _
      · rfl
    · rfl
  rw [h3, h2, h1]

theorem advanceNull_progress_of {f : Nat} {q : Processor n Tx} (h : Nullified f q.S q.view) :
    (advanceNull f q).1 = q.progress := by
  unfold advanceNull; rw [if_pos h]

theorem advanceNull_eq_of_not {f : Nat} {q : Processor n Tx} (h : ¬ Nullified f q.S q.view) :
    (advanceNull f q).1 = q := by
  unfold advanceNull; rw [if_neg h]

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

theorem advanceM_eq_of_nil {f : Nat} {i : Fin n} {q : Processor n Tx}
    (h : mNotarisedAt f q.S q.view = []) : (advanceM f i q).1 = q := by
  unfold advanceM; rw [h]

theorem mem_mNotarisedAt_of {f : Nat} {S : Finset (Msg n Tx)} {b : Block Tx} (hb : b ∈ votedBlocks S)
    (hM : MNotarised f S b) : b ∈ mNotarisedAt f S b.view := by
  simp only [mNotarisedAt, List.mem_filter, decide_eq_true_eq]
  exact ⟨hb, trivial, hM⟩

theorem nullifyTimeout_fires {Δ : Nat} {i : Fin n} {q : Processor n Tx} (ht : q.timer = 2 * Δ)
    (hnl : q.nullified = false) (hnot : q.notarised = none) :
    Msg.nullify i q.view ∈ (nullifyTimeout Δ i q).1.S := by
  unfold nullifyTimeout
  rw [if_pos ⟨ht, hnl, hnot⟩]
  exact mem_S_disseminate_fst i q _

theorem nullifyNoProgress_fires {f : Nat} {i : Fin n} {q : Processor n Tx} {c : Block Tx}
    (hnl : q.nullified = false) (hnot : q.notarised = some c)
    (hnp : NoProgress f q.S q.view (some c)) :
    Msg.nullify i q.view ∈ (nullifyNoProgress f i q).1.S := by
  unfold nullifyNoProgress
  rw [if_pos ⟨hnl, by rw [hnot]; exact Option.some_ne_none c, by rw [hnot]; exact hnp⟩]
  exact mem_S_disseminate_fst i q _

/-- 1 スロットの動作の後の局所状態は、st6 に 24〜28 行を適用したもの。 -/
theorem stepPair_fst (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (stepPair f Δ lead i p).1 = (nullifyNoProgress f i (st6 f Δ lead i p)).1 := rfl

theorem stepPair_view (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (stepPair f Δ lead i p).1.view = (st6 f Δ lead i p).view := by
  rw [stepPair_fst, nullifyNoProgress_view]

theorem S_st6_subset_stepPair (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st6 f Δ lead i p).S ⊆ (stepPair f Δ lead i p).1.S := by
  rw [stepPair_fst]; exact S_subset_nullifyNoProgress f i _

end Algo

end Minimmit
