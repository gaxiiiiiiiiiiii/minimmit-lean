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

/-- 19〜21 行。`advanceOnce` の、現在の view の nullification がない側。 -/
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
/-- 24〜28 行。 -/
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
  · exact S_subset_forwardNew _ _ _ (S_subset_nullifyNoProgress _ _ _ (mem_S_of_send_nullifyTimeout h))
  · exact S_subset_forwardNew _ _ _ (mem_S_of_send_nullifyNoProgress h)
  · exact mem_S_of_send_forwardNew h

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
theorem tick (h : LocalInv f i p) : LocalInv f i p.tick :=
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

theorem advanceOnce (h : LocalInv f i p) : LocalInv f i (advanceOnce f i p).1 := by
  rw [advanceOnce_eq]; split_ifs
  · exact h.progress
  · exact h.advanceM

theorem climb (h : LocalInv f i p) (fuel : Nat) : LocalInv f i (climb f i fuel p).1 := by
  induction fuel generalizing p with
  | zero => exact h
  | succ fuel ih =>
    simp only [Algo.climb]; split_ifs
    · exact ih h.advanceOnce
    · exact h

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
  (((((h.climb _).propose lead).voteProposal lead).nullifyTimeout Δ).nullifyNoProgress).forwardNew

end LocalInv


/-! ### 自分の提案についての不変量 -/

/-- S にある自分の署名付きブロックと、view・proposed の関係。 -/
structure PropInv (i : Fin n) (p : Processor n Tx) : Prop where
  /-- 自分のブロックの view は現在の view 以下。 -/
  prop_view : ∀ b, Msg.block i b ∈ p.S → b.view.val ≤ p.view.val
  /-- 現在の view の自分のブロックが S にあれば proposed。 -/
  prop_flag : ∀ b, Msg.block i b ∈ p.S → b.view = p.view → p.proposed = true
  /-- S にある自分のブロックで view が同じものは一致する。 -/
  prop_unique : ∀ b b', Msg.block i b ∈ p.S → Msg.block i b' ∈ p.S → b.view = b'.view → b = b'

namespace PropInv

variable {f : Nat} {i : Fin n} {p : Processor n Tx}

omit [DecidableEq Tx] in
theorem of_grow (h : PropInv i p) {q : Processor n Tx} (hv : q.view = p.view)
    (hp : q.proposed = p.proposed) (hblock : ∀ b, Msg.block i b ∈ q.S → Msg.block i b ∈ p.S) :
    PropInv i q := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb; rw [hv]; exact h.prop_view b (hblock b hb)
  · intro b hb hbv; rw [hp]; rw [hv] at hbv; exact h.prop_flag b (hblock b hb) hbv
  · intro b b' hb hb'; exact h.prop_unique b b' (hblock b hb) (hblock b' hb')

omit [DecidableEq Tx] in
theorem of_sgrows (h : PropInv i p) {q : Processor n Tx} (hg : p.SGrows q)
    (hblock : ∀ b, Msg.block i b ∈ q.S → Msg.block i b ∈ p.S) : PropInv i q :=
  h.of_grow hg.view hg.proposed hblock

omit [DecidableEq Tx] in
theorem tick (h : PropInv i p) : PropInv i p.tick := h.of_grow rfl rfl fun _ hb => hb

omit [DecidableEq Tx] in
theorem progress (h : PropInv i p) : PropInv i p.progress := by
  refine ⟨?_, ?_, fun b b' hb hb' => h.prop_unique b b' hb hb'⟩
  · intro b hb
    have := h.prop_view b hb
    simp only [Processor.progress]; omega
  · intro b hb hbv
    have := h.prop_view b hb
    rw [hbv] at this
    simp only [Processor.progress] at this
    omega

theorem send_of_not_block (h : PropInv i p) {m : Msg n Tx} (hm : ∀ b, m ≠ Msg.block i b)
    (j : Fin n) : PropInv i (p.send i m j) := by
  refine h.of_grow (Processor.send_view i p m j)
    (Processor.send_proposed_of_not_block i p m j fun b hb => absurd hb (hm b)) fun b hb => ?_
  exact (PreInv.mem_S_send_iff_of_ne i p j fun h' => hm b h'.symm).mp hb

theorem send_of_mem (h : PropInv i p) {m : Msg n Tx} (hm : m ∈ p.S) (j : Fin n) :
    PropInv i (p.send i m j) := by
  have hS : (p.send i m j).S = p.S := by
    rw [Processor.send_S]; split_ifs <;> simp [Finset.insert_eq_of_mem hm]
  refine ⟨?_, ?_, ?_⟩
  · intro b hb; rw [hS] at hb; rw [Processor.send_view]; exact h.prop_view b hb
  · intro b hb hbv
    rw [hS] at hb; rw [Processor.send_view] at hbv
    have := h.prop_flag b hb hbv
    by_cases hmb : ∃ b', m = Msg.block i b'
    · obtain ⟨b', rfl⟩ := hmb
      rw [Processor.send_block_proposed]
      split_ifs
      · rfl
      · exact this
    · rw [Processor.send_proposed_of_not_block i p m j fun b' hb' => absurd ⟨b', hb'⟩ hmb]
      exact this
  · intro b b' hb hb'; rw [hS] at hb hb'; exact h.prop_unique b b' hb hb'

/-- 現在の view のブロックの送信。同じ view の自分のブロックは S にそれしかない。 -/
theorem send_block (h : PropInv i p) {b : Block Tx} (hb : b.view = p.view)
    (huniq : ∀ b', Msg.block i b' ∈ p.S → b'.view = p.view → b' = b) (j : Fin n) :
    PropInv i (p.send i (Msg.block i b) j) := by
  have hS : ∀ b', Msg.block i b' ∈ (p.send i (Msg.block i b) j).S →
      b' = b ∨ Msg.block i b' ∈ p.S := by
    intro b' hb'
    rw [Processor.send_S] at hb'
    split_ifs at hb'
    · rcases Finset.mem_insert.mp hb' with hb' | hb'
      · exact Or.inl (by cases hb'; rfl)
      · exact Or.inr hb'
    · exact Or.inr hb'
  have hview := Processor.send_view i p (Msg.block i b) j
  refine ⟨?_, ?_, ?_⟩
  · intro b' hb'
    rw [hview]
    rcases hS b' hb' with rfl | hb'
    · rw [hb]
    · exact h.prop_view b' hb'
  · intro b' _ _
    rw [Processor.send_block_proposed, if_pos hb]
  · intro b' b'' hb' hb'' hvv
    rcases hS b' hb' with rfl | hb₁ <;> rcases hS b'' hb'' with rfl | hb₂
    · rfl
    · exact (huniq b'' hb₂ (hvv.symm.trans hb)).symm
    · exact huniq b' hb₁ (hvv.trans hb)
    · exact h.prop_unique b' b'' hb₁ hb₂ hvv

theorem foldl_send_of_not_block (h : PropInv i p) {m : Msg n Tx} (hm : ∀ b, m ≠ Msg.block i b)
    (l : List (Fin n)) : PropInv i (l.foldl (fun p j => p.send i m j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih => exact ih (h.send_of_not_block hm j)

theorem foldl_send_of_mem (h : PropInv i p) {m : Msg n Tx} (hm : m ∈ p.S) (l : List (Fin n)) :
    PropInv i (l.foldl (fun p j => p.send i m j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih => exact ih (h.send_of_mem hm j) (Processor.S_subset_send i p m j hm)

theorem foldl_send_block (h : PropInv i p) {b : Block Tx} (hb : b.view = p.view)
    (huniq : ∀ b', Msg.block i b' ∈ p.S → b'.view = p.view → b' = b) (l : List (Fin n)) :
    PropInv i (l.foldl (fun p j => p.send i (Msg.block i b) j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih =>
    refine ih (h.send_block hb huniq j) (by rw [Processor.send_view]; exact hb) ?_
    intro b' hb' hbv
    rw [Processor.send_view] at hbv
    rw [Processor.send_S] at hb'
    split_ifs at hb'
    · rcases Finset.mem_insert.mp hb' with hb' | hb'
      · cases hb'; rfl
      · exact huniq b' hb' hbv
    · exact huniq b' hb' hbv

theorem disseminate_of_not_block (h : PropInv i p) {m : Msg n Tx} (hm : ∀ b, m ≠ Msg.block i b) :
    PropInv i (disseminate i p m).1 := by
  rw [disseminate_fst]; exact h.foldl_send_of_not_block hm _

theorem disseminate_of_mem (h : PropInv i p) {m : Msg n Tx} (hm : m ∈ p.S) :
    PropInv i (disseminate i p m).1 := by
  rw [disseminate_fst]; exact h.foldl_send_of_mem hm _

/-- まだ提案していないときの、現在の view のブロックの提案。 -/
theorem disseminate_block (h : PropInv i p) {b : Block Tx} (hb : b.view = p.view)
    (hp : p.proposed = false) : PropInv i (disseminate i p (Msg.block i b)).1 := by
  rw [disseminate_fst]
  refine h.foldl_send_block hb (fun b' hb' hbv => ?_) _
  have := h.prop_flag b' hb' hbv
  rw [hp] at this; cases this

theorem disseminateAll_of_mem (h : PropInv i p) {ms : List (Msg n Tx)} (hm : ∀ m ∈ ms, m ∈ p.S) :
    PropInv i (disseminateAll i p ms).1 := by
  rw [disseminateAll_fst]
  induction ms generalizing p with
  | nil => exact h
  | cons m ms ih =>
    exact ih (h.disseminate_of_mem (hm m (List.mem_cons_self ..))) fun m' hm' =>
      S_subset_disseminate_fst i p m (hm m' (List.mem_cons_of_mem _ hm'))

theorem forwardNew (h : PropInv i p) : PropInv i (forwardNew f i p).1 := by
  rw [forwardNew_eq]
  exact h.disseminateAll_of_mem fun m hm => mem_S_of_mem_forwardMsgs hm

theorem propose (h : PropInv i p) (lead : View → Fin n) : PropInv i (propose f lead i p).1 := by
  unfold Algo.propose
  split_ifs with hg
  · exact h.disseminate_block rfl hg.2
  · exact h

theorem voteProposal (h : PropInv i p) (lead : View → Fin n) :
    PropInv i (voteProposal f lead i p).1 := by
  unfold Algo.voteProposal
  rcases proposals lead p.S p.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · exact h
  · simp only
    split_ifs
    · exact h.disseminate_of_not_block fun _ h => by cases h
    · exact h
  · exact h

theorem nullifyTimeout (h : PropInv i p) (Δ : Nat) : PropInv i (nullifyTimeout Δ i p).1 := by
  unfold Algo.nullifyTimeout
  split_ifs
  · exact h.disseminate_of_not_block fun _ h => by cases h
  · exact h

theorem advanceM (h : PropInv i p) : PropInv i (advanceM f i p).1 := by
  unfold Algo.advanceM
  rcases mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · exact h
  · simp only
    split_ifs
    · exact (h.disseminate_of_not_block fun _ h => by cases h).progress
    · exact h.progress

theorem advanceOnce (h : PropInv i p) : PropInv i (advanceOnce f i p).1 := by
  rw [advanceOnce_eq]; split_ifs
  · exact h.progress
  · exact h.advanceM

theorem climb (h : PropInv i p) (fuel : Nat) : PropInv i (climb f i fuel p).1 := by
  induction fuel generalizing p with
  | zero => exact h
  | succ fuel ih =>
    simp only [Algo.climb]; split_ifs
    · exact ih h.advanceOnce
    · exact h

theorem nullifyNoProgress (h : PropInv i p) : PropInv i (nullifyNoProgress f i p).1 := by
  unfold Algo.nullifyNoProgress
  split_ifs
  · exact h.disseminate_of_not_block fun _ h => by cases h
  · exact h

/-- Algorithm 1 の 1 スロット分の動作は不変量を保つ。 -/
theorem stepPair (h : PropInv i p) (Δ : Nat) (lead : View → Fin n) :
    PropInv i (stepPair f Δ lead i p).1 :=
  (((((h.climb _).propose lead).voteProposal lead).nullifyTimeout Δ).nullifyNoProgress).forwardNew

end PropInv

/-! ### 段ごとの入力状態と、送信の出所 -/

section Stages

variable (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx)

/-- 各段の入力となる局所状態。st1 は 16〜21 行（登り）の後、st2 は 5〜7 行の後、st3 は
    9〜11 行の後、st4 は 13〜14 行の後、st5 は 24〜28 行の後。最後に 2〜3 行。 -/
noncomputable def st1 : Processor n Tx := (climb f i (maxView p.S + 1) p).1
noncomputable def st2 : Processor n Tx := (propose f lead i (st1 f i p)).1
noncomputable def st3 : Processor n Tx := (voteProposal f lead i (st2 f lead i p)).1
noncomputable def st4 : Processor n Tx := (nullifyTimeout Δ i (st3 f lead i p)).1
noncomputable def st5 : Processor n Tx := (nullifyNoProgress f i (st4 f Δ lead i p)).1

theorem stepPair_snd : (stepPair f Δ lead i p).2 =
    (climb f i (maxView p.S + 1) p).2 ++ (propose f lead i (st1 f i p)).2
      ++ (voteProposal f lead i (st2 f lead i p)).2 ++ (nullifyTimeout Δ i (st3 f lead i p)).2
      ++ (nullifyNoProgress f i (st4 f Δ lead i p)).2 ++ (forwardNew f i (st5 f Δ lead i p)).2 := rfl

theorem stepPair_fst : (stepPair f Δ lead i p).1 = (forwardNew f i (st5 f Δ lead i p)).1 := rfl

/-- 2〜3 行の転送を除いた動作の列。 -/
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

theorem propose_notarised (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (propose f lead i p).1.notarised = p.notarised := by
  unfold propose; split_ifs
  · rw [disseminate_fst]
    exact PreInv.foldl_send_notarised_of_not_vote (fun _ h => by cases h) _ _
  · rfl

theorem propose_nullified (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (propose f lead i p).1.nullified = p.nullified := by
  unfold propose; split_ifs
  · rw [disseminate_fst]
    exact PreInv.foldl_send_nullified_of_not_nullify (fun _ h => by cases h) _ _
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

/-- 各段の view。5〜7 行以降は view を変えない。 -/
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

/-! #### 登り: 16〜21 行の繰り返し -/

omit [DecidableEq Tx] in
theorem mem_nullifyViews {S : Finset (Msg n Tx)} {q : Fin n} {v : View} (h : Msg.nullify q v ∈ S) :
    v ∈ nullifyViews S := by
  simp only [nullifyViews, List.mem_dedup, List.mem_filterMap, Finset.mem_toList]
  exact ⟨Msg.nullify q v, h, rfl⟩

theorem mem_votedBlocks {S : Finset (Msg n Tx)} {q : Fin n} {b : Block Tx} (h : Msg.vote q b ∈ S) :
    b ∈ votedBlocks S := by
  simp only [votedBlocks, List.mem_dedup, List.mem_filterMap, Finset.mem_toList]
  exact ⟨Msg.vote q b, h, rfl⟩

theorem exists_vote_of_mem_votedBlocks {S : Finset (Msg n Tx)} {b : Block Tx}
    (h : b ∈ votedBlocks S) : ∃ q, Msg.vote q b ∈ S := by
  simp only [votedBlocks, List.mem_dedup, List.mem_filterMap, Finset.mem_toList] at h
  obtain ⟨m, hm, hmb⟩ := h
  cases m with
  | block q b' => simp at hmb
  | vote q b' => simp at hmb; subst hmb; exact ⟨q, hm⟩
  | nullify q v => simp at hmb
  | tx tr => simp at hmb

theorem mem_votedBlocks_of_mem_mNotarisedAt {f : Nat} {S : Finset (Msg n Tx)} {v : View}
    {b : Block Tx} (h : b ∈ mNotarisedAt f S v) : b ∈ votedBlocks S := by
  simp only [mNotarisedAt, List.mem_filter] at h
  exact h.1

theorem mem_mNotarisedAt_of {f : Nat} {S : Finset (Msg n Tx)} {b : Block Tx} (hb : b ∈ votedBlocks S)
    (hM : MNotarised f S b) : b ∈ mNotarisedAt f S b.view := by
  simp only [mNotarisedAt, List.mem_filter, decide_eq_true_eq]
  exact ⟨hb, trivial, hM⟩

theorem viewNum_le_maxView {S : Finset (Msg n Tx)} {m : Msg n Tx} (h : m ∈ S) :
    m.viewNum ≤ maxView S :=
  Finset.le_sup h

/-- 証明書のある view は、S にある message の view を超えない。 -/
theorem hasCert_le_maxView {f : Nat} {S : Finset (Msg n Tx)} {v : View} (h : HasCert f S v) :
    v.val ≤ maxView S := by
  rcases h with h | h
  · obtain ⟨q, hq⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos _) h)
    exact viewNum_le_maxView (mem_nullifiers.mp hq)
  · obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨q, hq⟩ := exists_vote_of_mem_votedBlocks (mem_votedBlocks_of_mem_mNotarisedAt hb)
    have h1 : b.view.val ≤ maxView S := viewNum_le_maxView hq
    rw [(mem_mNotarisedAt hb).1] at h1
    exact h1

theorem HasCert.mono {f : Nat} {S S' : Finset (Msg n Tx)} {v : View} (h : HasCert f S v)
    (hS : S ⊆ S') : HasCert f S' v := by
  rcases h with h | h
  · exact Or.inl (h.mono hS)
  · right
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ h
    have hb' := mem_mNotarisedAt hb
    obtain ⟨q, hq⟩ := exists_vote_of_mem_votedBlocks (mem_votedBlocks_of_mem_mNotarisedAt hb)
    apply List.ne_nil_of_mem (a := b)
    rw [← hb'.1]
    exact mem_mNotarisedAt_of (mem_votedBlocks (hS hq)) (hb'.2.mono hS)

/-- S' が S に、view が w 未満のブロックへの票を足しただけなら、view w の証明書は S にもある。 -/
theorem hasCert_of_votes_lt {f : Nat} {i : Fin n} {S S' : Finset (Msg n Tx)} {w : View}
    (hS : S ⊆ S') (hnew : ∀ m ∈ S', m ∈ S ∨ ∃ b, m = Msg.vote i b ∧ b.view.val < w.val)
    (h : HasCert f S' w) : HasCert f S w := by
  rcases h with h | h
  · left
    refine h.trans (Finset.card_le_card fun q hq => ?_)
    rw [mem_nullifiers] at hq ⊢
    rcases hnew _ hq with hq | ⟨b, hb, _⟩
    · exact hq
    · cases hb
  · right
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ h
    have hb' := mem_mNotarisedAt hb
    have hvote : ∀ q, Msg.vote q b ∈ S' → Msg.vote q b ∈ S := by
      intro q hq
      rcases hnew _ hq with hq | ⟨b', hb'', hlt⟩
      · exact hq
      · injection hb'' with _ hbb
        subst hbb
        rw [hb'.1] at hlt
        exact absurd hlt (lt_irrefl _)
    obtain ⟨q, hq⟩ := exists_vote_of_mem_votedBlocks (mem_votedBlocks_of_mem_mNotarisedAt hb)
    have hM : MNotarised f S b := by
      rcases hb'.2 with hg | hM
      · exact Or.inl hg
      · right
        refine hM.trans (Finset.card_le_card fun q' hq' => ?_)
        rw [mem_voters] at hq' ⊢
        exact hvote q' hq'
    apply List.ne_nil_of_mem (a := b)
    rw [← hb'.1]
    exact mem_mNotarisedAt_of (mem_votedBlocks (hvote q hq)) hM

theorem advanceOnce_view (f : Nat) (i : Fin n) (p : Processor n Tx) :
    (advanceOnce f i p).1.view = p.view ∨ (advanceOnce f i p).1.view.val = p.view.val + 1 := by
  rw [advanceOnce_eq]; split_ifs
  · exact Or.inr rfl
  · exact advanceM_view f i p

theorem advanceOnce_view_succ {f : Nat} (i : Fin n) {p : Processor n Tx}
    (hc : HasCert f p.S p.view) : (advanceOnce f i p).1.view.val = p.view.val + 1 := by
  rw [advanceOnce_eq]; split_ifs with hN
  · rfl
  · exact advanceM_view_succ_of_ne_nil (hc.resolve_left hN)

theorem advanceOnce_eq_of_not {f : Nat} (i : Fin n) {p : Processor n Tx}
    (hc : ¬ HasCert f p.S p.view) : advanceOnce f i p = (p, []) := by
  have hM : mNotarisedAt f p.S p.view = [] := by
    by_contra h; exact hc (Or.inr h)
  rw [advanceOnce_eq, if_neg (fun h => hc (Or.inl h))]
  unfold advanceM; rw [hM]

theorem climb_succ_of {f : Nat} (i : Fin n) {p : Processor n Tx} (hc : HasCert f p.S p.view)
    (fuel : Nat) :
    climb f i (fuel + 1) p
      = ((climb f i fuel (advanceOnce f i p).1).1,
          (advanceOnce f i p).2 ++ (climb f i fuel (advanceOnce f i p).1).2) := by
  simp only [climb]; rw [if_pos hc]

theorem climb_of_not {f : Nat} (i : Fin n) {p : Processor n Tx} (hc : ¬ HasCert f p.S p.view)
    (fuel : Nat) : climb f i fuel p = (p, []) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [climb]; rw [if_neg hc]

theorem view_le_climb (f : Nat) (i : Fin n) (fuel : Nat) (p : Processor n Tx) :
    p.view.val ≤ (climb f i fuel p).1.view.val := by
  induction fuel generalizing p with
  | zero => exact le_refl _
  | succ fuel ih =>
    by_cases hc : HasCert f p.S p.view
    · rw [climb_succ_of i hc]
      have h1 := advanceOnce_view_succ (f := f) i hc
      have h2 := ih (advanceOnce f i p).1
      show p.view.val ≤ (climb f i fuel (advanceOnce f i p).1).1.view.val
      omega
    · rw [climb_of_not i hc]

/-- view が変わらなければ、登りは何もしていない。 -/
theorem climb_eq_of_view {f : Nat} {i : Fin n} {fuel : Nat} {p : Processor n Tx}
    (h : (climb f i fuel p).1.view = p.view) : climb f i fuel p = (p, []) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    by_cases hc : HasCert f p.S p.view
    · exfalso
      rw [climb_succ_of i hc] at h
      have h1 := advanceOnce_view_succ (f := f) i hc
      have h2 := view_le_climb f i fuel (advanceOnce f i p).1
      have h3 : (climb f i fuel (advanceOnce f i p).1).1.view.val = p.view.val :=
        congrArg View.val h
      omega
    · exact climb_of_not i hc _

/-- 燃料を使い切ったか、現在の view の証明書がなくなって止まったか。 -/
theorem climb_exhaust (f : Nat) (i : Fin n) (fuel : Nat) (p : Processor n Tx) :
    (climb f i fuel p).1.view.val = p.view.val + fuel
      ∨ ¬ HasCert f (climb f i fuel p).1.S (climb f i fuel p).1.view := by
  induction fuel generalizing p with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
    by_cases hc : HasCert f p.S p.view
    · rw [climb_succ_of i hc]
      rcases ih (advanceOnce f i p).1 with h | h
      · left
        show (climb f i fuel (advanceOnce f i p).1).1.view.val = p.view.val + (fuel + 1)
        rw [h, advanceOnce_view_succ i hc]; omega
      · exact Or.inr h
    · rw [climb_of_not i hc]; exact Or.inr hc

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

theorem mem_S_advanceM {f : Nat} {i : Fin n} {q : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (advanceM f i q).1.S) :
    m ∈ q.S ∨ ∃ b, m = Msg.vote i b ∧ b ∈ mNotarisedAt f q.S q.view
      ∧ Action.send (Msg.vote i b) i ∈ (advanceM f i q).2 := by
  unfold advanceM at hm ⊢
  generalize hl : mNotarisedAt f q.S q.view = l at hm ⊢
  rcases l with _ | ⟨b, l⟩
  · exact Or.inl hm
  · simp only at hm ⊢
    split_ifs at hm ⊢
    · simp only [Processor.progress] at hm
      exact (mem_S_disseminate_or i q _ hm).imp_right fun h =>
        ⟨b, h, List.mem_cons_self .., List.mem_append_left _ (mem_disseminate_snd.mpr ⟨i, rfl⟩)⟩
    · exact Or.inl hm

theorem mem_S_advanceOnce {f : Nat} {i : Fin n} {q : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (advanceOnce f i q).1.S) :
    m ∈ q.S ∨ ∃ b, m = Msg.vote i b ∧ b ∈ mNotarisedAt f q.S q.view
      ∧ Action.send (Msg.vote i b) i ∈ (advanceOnce f i q).2 := by
  rw [advanceOnce_eq] at hm ⊢; split_ifs at hm ⊢
  · exact Or.inl hm
  · exact mem_S_advanceM hm

/-- 登りの後の S にある message は、前からあったか、登りで出した自分の票。票の view は
    登りの後の view より小さい。 -/
theorem mem_S_climb {f : Nat} {i : Fin n} {fuel : Nat} {q : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (climb f i fuel q).1.S) :
    m ∈ q.S ∨ ∃ b, m = Msg.vote i b ∧ b.view.val < (climb f i fuel q).1.view.val
      ∧ ∃ j, Action.send (Msg.vote i b) j ∈ (climb f i fuel q).2 := by
  induction fuel generalizing q with
  | zero => exact Or.inl hm
  | succ fuel ih =>
    by_cases hc : HasCert f q.S q.view
    · rw [climb_succ_of i hc] at hm ⊢
      rcases ih hm with hm | ⟨b, rfl, hb, j, hj⟩
      · rcases mem_S_advanceOnce hm with hm | ⟨b, rfl, hb, hs⟩
        · exact Or.inl hm
        · right
          refine ⟨b, rfl, ?_, i, List.mem_append_left _ hs⟩
          have h1 := (mem_mNotarisedAt hb).1
          have h2 := advanceOnce_view_succ (f := f) i hc
          have h3 := view_le_climb f i fuel (advanceOnce f i q).1
          show b.view.val < (climb f i fuel (advanceOnce f i q).1).1.view.val
          rw [h1]; omega
      · exact Or.inr ⟨b, rfl, hb, j, List.mem_append_right _ hj⟩
    · rw [climb_of_not i hc] at hm ⊢; exact Or.inl hm

theorem maxView_advanceOnce (f : Nat) (i : Fin n) (p : Processor n Tx) :
    maxView (advanceOnce f i p).1.S ≤ maxView p.S := by
  apply Finset.sup_le
  intro m hm
  rcases mem_S_advanceOnce hm with hm | ⟨b, rfl, hb, _⟩
  · exact viewNum_le_maxView hm
  · obtain ⟨q, hq⟩ := exists_vote_of_mem_votedBlocks (mem_votedBlocks_of_mem_mNotarisedAt hb)
    have h1 : b.view.val ≤ maxView p.S := viewNum_le_maxView hq
    exact h1

theorem maxView_climb (f : Nat) (i : Fin n) (fuel : Nat) (p : Processor n Tx) :
    maxView (climb f i fuel p).1.S ≤ maxView p.S := by
  induction fuel generalizing p with
  | zero => exact le_refl _
  | succ fuel ih =>
    by_cases hc : HasCert f p.S p.view
    · rw [climb_succ_of i hc]
      exact (ih _).trans (maxView_advanceOnce f i p)
    · rw [climb_of_not i hc]

/-- 登りで通過した view の証明書は、登る前の S にある。 -/
theorem climb_certs (f : Nat) (i : Fin n) (fuel : Nat) (p : Processor n Tx) :
    ∀ w : View, p.view.val ≤ w.val → w.val < (climb f i fuel p).1.view.val → HasCert f p.S w := by
  induction fuel generalizing p with
  | zero => intro w h1 h2; exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  | succ fuel ih =>
    intro w h1 h2
    by_cases hc : HasCert f p.S p.view
    · rw [climb_succ_of i hc] at h2
      have hv := advanceOnce_view_succ (f := f) i hc
      by_cases hw : w.val = p.view.val
      · rw [View.val_injective hw]; exact hc
      · have h1' : (advanceOnce f i p).1.view.val ≤ w.val := by omega
        have h2' : w.val < (climb f i fuel (advanceOnce f i p).1).1.view.val := h2
        have hw' := ih (advanceOnce f i p).1 w h1' h2'
        refine hasCert_of_votes_lt (i := i) (S_subset_advanceOnce f i p) ?_ hw'
        intro m hm
        rcases mem_S_advanceOnce hm with hm | ⟨b, rfl, hb, _⟩
        · exact Or.inl hm
        · right; refine ⟨b, rfl, ?_⟩
          rw [(mem_mNotarisedAt hb).1]; omega
    · rw [climb_of_not i hc] at h2
      exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

/-- v 未満の各 view の証明書があり、燃料が足りれば、登りは v 以上に達する。 -/
theorem climb_reaches (f : Nat) (i : Fin n) (fuel : Nat) (p : Processor n Tx) (v : View)
    (hcerts : ∀ w : View, p.view.val ≤ w.val → w.val < v.val → HasCert f p.S w)
    (hfuel : v.val ≤ p.view.val + fuel) : v.val ≤ (climb f i fuel p).1.view.val := by
  induction fuel generalizing p with
  | zero => exact hfuel
  | succ fuel ih =>
    by_cases hlt : p.view.val < v.val
    · have hc : HasCert f p.S p.view := hcerts p.view (le_refl _) hlt
      rw [climb_succ_of i hc]
      have hv := advanceOnce_view_succ (f := f) i hc
      show v.val ≤ (climb f i fuel (advanceOnce f i p).1).1.view.val
      apply ih
      · intro w h1 h2
        exact (hcerts w (by omega) h2).mono (S_subset_advanceOnce f i p)
      · omega
    · exact le_trans (not_lt.mp hlt) (view_le_climb f i (fuel + 1) p)

/-- 登りで view w を通過する中間状態 q。q の S は登る前の S に、w 未満の view への自分の票を
    足したもので、w の証明書を持つ。 -/
theorem climb_pass {f : Nat} {i : Fin n} {fuel : Nat} {p : Processor n Tx} (hL : LocalInv f i p)
    {w : View} (h1 : p.view.val ≤ w.val) (h2 : w.val < (climb f i fuel p).1.view.val) :
    ∃ q, LocalInv f i q ∧ q.view = w ∧ p.S ⊆ q.S ∧ HasCert f q.S w
      ∧ (∀ m ∈ q.S, m ∈ p.S ∨ ∃ b', m = Msg.vote i b' ∧ b'.view.val < w.val)
      ∧ (advanceOnce f i q).1.S ⊆ (climb f i fuel p).1.S
      ∧ (∀ m j, Action.send m j ∈ (advanceOnce f i q).2 → Action.send m j ∈ (climb f i fuel p).2) := by
  induction fuel generalizing p with
  | zero => exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  | succ fuel ih =>
    by_cases hc : HasCert f p.S p.view
    · rw [climb_succ_of i hc] at h2 ⊢
      have hv := advanceOnce_view_succ (f := f) i hc
      by_cases hw : w.val = p.view.val
      · refine ⟨p, hL, (View.val_injective hw).symm, Finset.Subset.refl _, ?_,
          fun m hm => Or.inl hm, S_subset_climb f i fuel _, fun m j hj => List.mem_append_left _ hj⟩
        rw [View.val_injective hw]; exact hc
      · have h1' : (advanceOnce f i p).1.view.val ≤ w.val := by omega
        have h2' : w.val < (climb f i fuel (advanceOnce f i p).1).1.view.val := h2
        obtain ⟨q, hLq, hqv, hsub, hcert, hnew, hS, hsend⟩ := ih hL.advanceOnce h1' h2'
        refine ⟨q, hLq, hqv, (S_subset_advanceOnce f i p).trans hsub, hcert, ?_, hS,
          fun m j hj => List.mem_append_right _ (hsend m j hj)⟩
        intro m hm
        rcases hnew m hm with hm | hm
        · rcases mem_S_advanceOnce hm with hm | ⟨b', rfl, hb', _⟩
          · exact Or.inl hm
          · right; refine ⟨b', rfl, ?_⟩
            rw [(mem_mNotarisedAt hb').1]; omega
        · exact Or.inr hm
    · rw [climb_of_not i hc] at h2
      exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

/-- nullification がなく M-notarisation があり、未投票で nullify も出していなければ、
    19〜21 行は M-notarisation のあるブロックに投票する。 -/
theorem advanceOnce_vote_of {f : Nat} (i : Fin n) {q : Processor n Tx}
    (hN : ¬ Nullified f q.S q.view) (hM : mNotarisedAt f q.S q.view ≠ [])
    (hn : q.notarised = none) (hnl : q.nullified = false) :
    ∃ b ∈ mNotarisedAt f q.S q.view, Action.send (Msg.vote i b) i ∈ (advanceOnce f i q).2 := by
  rw [advanceOnce_eq, if_neg hN]
  unfold advanceM
  generalize hl : mNotarisedAt f q.S q.view = l at hM ⊢
  rcases l with _ | ⟨b, l⟩
  · exact absurd rfl hM
  · simp only
    rw [if_pos ⟨hn, hnl⟩]
    exact ⟨b, List.mem_cons_self .., List.mem_append_left _ (mem_disseminate_snd.mpr ⟨i, rfl⟩)⟩

/-- 証明書があって進んだ後の timer・proposed・notarised・nullified。 -/
theorem advanceOnce_fields {f : Nat} (i : Fin n) {p : Processor n Tx} (hc : HasCert f p.S p.view) :
    (advanceOnce f i p).1.timer = 0 ∧ (advanceOnce f i p).1.proposed = false
      ∧ (advanceOnce f i p).1.notarised = none ∧ (advanceOnce f i p).1.nullified = false := by
  rw [advanceOnce_eq]; split_ifs with hN
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · unfold advanceM
    generalize hl : mNotarisedAt f p.S p.view = l
    rcases l with _ | ⟨b, l⟩
    · exact absurd hl (hc.resolve_left hN)
    · simp only; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- 登りは何もしないか、timer を 0 にし proposed を false にする。 -/
theorem climb_eq_or (f : Nat) (i : Fin n) (fuel : Nat) (p : Processor n Tx) :
    climb f i fuel p = (p, [])
      ∨ ((climb f i fuel p).1.timer = 0 ∧ (climb f i fuel p).1.proposed = false) := by
  induction fuel generalizing p with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
    by_cases hc : HasCert f p.S p.view
    · right
      rw [climb_succ_of i hc]
      rcases ih (advanceOnce f i p).1 with h | h
      · show (climb f i fuel (advanceOnce f i p).1).1.timer = 0
          ∧ (climb f i fuel (advanceOnce f i p).1).1.proposed = false
        rw [h]; exact ⟨(advanceOnce_fields i hc).1, (advanceOnce_fields i hc).2.1⟩
      · exact h
    · exact Or.inl (climb_of_not i hc _)

theorem st1_eq_or (f : Nat) (i : Fin n) (p : Processor n Tx) :
    st1 f i p = p ∨ ((st1 f i p).timer = 0 ∧ (st1 f i p).proposed = false) := by
  rcases climb_eq_or f i (maxView p.S + 1) p with h | h
  · left; show (climb f i (maxView p.S + 1) p).1 = p; rw [h]
  · exact Or.inr h

/-! #### st1: 登りの後の状態 -/

theorem view_le_st1 (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.view.val ≤ (st1 f i p).view.val :=
  view_le_climb f i _ p

/-- view が変わらなければ、16〜21 行は何もしていない。 -/
theorem st1_eq_of_view {f : Nat} {i : Fin n} {p : Processor n Tx}
    (h : (st1 f i p).view = p.view) : st1 f i p = p := by
  show (climb f i (maxView p.S + 1) p).1 = p
  rw [climb_eq_of_view h]

theorem st1_certs {f : Nat} {i : Fin n} {p : Processor n Tx} {w : View} (h1 : p.view.val ≤ w.val)
    (h2 : w.val < (st1 f i p).view.val) : HasCert f p.S w :=
  climb_certs f i _ p w h1 h2

theorem view_lt_st1_of_hasCert {f : Nat} (i : Fin n) {p : Processor n Tx}
    (hc : HasCert f p.S p.view) : p.view.val < (st1 f i p).view.val := by
  show p.view.val < (climb f i (maxView p.S + 1) p).1.view.val
  rw [climb_succ_of i hc]
  have h1 := advanceOnce_view_succ (f := f) i hc
  have h2 := view_le_climb f i (maxView p.S) (advanceOnce f i p).1
  show p.view.val < (climb f i (maxView p.S) (advanceOnce f i p).1).1.view.val
  omega

/-- v 未満の各 view の証明書があれば、登りは v 以上に達する。 -/
theorem st1_reaches {f : Nat} (i : Fin n) {p : Processor n Tx} {v : View}
    (hcerts : ∀ w : View, p.view.val ≤ w.val → w.val < v.val → HasCert f p.S w) :
    v.val ≤ (st1 f i p).view.val := by
  apply climb_reaches f i _ p v hcerts
  by_cases hlt : p.view.val < v.val
  · have h1 : (⟨v.val - 1⟩ : View).val ≤ maxView p.S :=
      hasCert_le_maxView (hcerts ⟨v.val - 1⟩ (by show p.view.val ≤ v.val - 1; omega)
        (by show v.val - 1 < v.val; omega))
    have h2 : v.val - 1 ≤ maxView p.S := h1
    omega
  · omega

/-- 登りの後は、現在の view の証明書がない。 -/
theorem st1_quiescent (f : Nat) (i : Fin n) (p : Processor n Tx) :
    ¬ HasCert f (st1 f i p).S (st1 f i p).view := by
  rcases climb_exhaust f i (maxView p.S + 1) p with h | h
  · intro hc
    have h1 := hasCert_le_maxView hc
    have h2 : maxView (st1 f i p).S ≤ maxView p.S := maxView_climb f i _ p
    have h3 : (st1 f i p).view.val = p.view.val + (maxView p.S + 1) := h
    omega
  · exact h

/-- 段を進めても S は減らない。 -/
theorem S_subset_st1 (f : Nat) (i : Fin n) (p : Processor n Tx) : p.S ⊆ (st1 f i p).S :=
  S_subset_climb f i _ p

theorem S_subset_st2 (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (st2 f lead i p).S :=
  (S_subset_st1 f i p).trans (S_subset_propose f lead i _)

theorem S_subset_st3 (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (st3 f lead i p).S :=
  (S_subset_st2 f lead i p).trans (S_subset_voteProposal f lead i _)

theorem S_subset_st4 (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (st4 f Δ lead i p).S :=
  (S_subset_st3 f lead i p).trans (S_subset_nullifyTimeout Δ i _)

theorem S_subset_st5 (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    p.S ⊆ (st5 f Δ lead i p).S :=
  (S_subset_st4 f Δ lead i p).trans (S_subset_nullifyNoProgress f i _)

theorem S_st3_subset_st4 (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st3 f lead i p).S ⊆ (st4 f Δ lead i p).S :=
  S_subset_nullifyTimeout Δ i _

theorem S_st4_subset_st5 (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st4 f Δ lead i p).S ⊆ (st5 f Δ lead i p).S :=
  S_subset_nullifyNoProgress f i _

theorem S_st3_subset_st5 (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st3 f lead i p).S ⊆ (st5 f Δ lead i p).S :=
  (S_st3_subset_st4 f Δ lead i p).trans (S_st4_subset_st5 f Δ lead i p)

theorem S_st2_subset_st5 (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st2 f lead i p).S ⊆ (st5 f Δ lead i p).S :=
  (S_subset_voteProposal f lead i _).trans (S_st3_subset_st5 f Δ lead i p)

theorem S_st1_subset_st5 (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st1 f i p).S ⊆ (st5 f Δ lead i p).S :=
  (S_subset_propose f lead i _).trans ((S_subset_voteProposal f lead i _).trans
    (S_st3_subset_st5 f Δ lead i p))

theorem stepPair_S (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (stepPair f Δ lead i p).1.S = (st5 f Δ lead i p).S := by
  rw [stepPair_fst, forwardNew_S]

/-! #### 各段の後の S の中身 -/

theorem mem_S_forwardNew {f : Nat} {i : Fin n} {q : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (forwardNew f i q).1.S) : m ∈ q.S := by
  rw [forwardNew_S] at hm; exact hm

theorem mem_S_propose {f : Nat} {lead : View → Fin n} {i : Fin n} {q : Processor n Tx}
    {m : Msg n Tx} (hm : m ∈ (propose f lead i q).1.S) :
    m ∈ q.S ∨ ∃ b, m = Msg.block i b ∧ Action.send (Msg.block i b) i ∈ (propose f lead i q).2 := by
  unfold propose at hm ⊢
  split_ifs at hm ⊢
  · exact (mem_S_disseminate_or i q _ hm).imp_right fun h => ⟨_, h, mem_disseminate_snd.mpr ⟨i, rfl⟩⟩
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
    (hm : m ∈ (nullifyTimeout Δ i q).1.S) :
    m ∈ q.S ∨ ∃ v, m = Msg.nullify i v ∧ Action.send (Msg.nullify i v) i ∈ (nullifyTimeout Δ i q).2 := by
  unfold nullifyTimeout at hm ⊢
  split_ifs at hm ⊢
  · exact (mem_S_disseminate_or i q _ hm).imp_right fun h => ⟨_, h, mem_disseminate_snd.mpr ⟨i, rfl⟩⟩
  · exact Or.inl hm

theorem mem_S_nullifyNoProgress {f : Nat} {i : Fin n} {q : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (nullifyNoProgress f i q).1.S) :
    m ∈ q.S ∨ ∃ v, m = Msg.nullify i v ∧ Action.send (Msg.nullify i v) i ∈ (nullifyNoProgress f i q).2 := by
  unfold nullifyNoProgress at hm ⊢
  split_ifs at hm ⊢
  · exact (mem_S_disseminate_or i q _ hm).imp_right fun h => ⟨_, h, mem_disseminate_snd.mpr ⟨i, rfl⟩⟩
  · exact Or.inl hm

theorem mem_S_st1 {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (st1 f i p).S) :
    m ∈ p.S ∨ ∃ b, m = Msg.vote i b ∧ b.view.val < (st1 f i p).view.val
      ∧ ∃ j, Action.send (Msg.vote i b) j ∈ (climb f i (maxView p.S + 1) p).2 :=
  mem_S_climb hm

theorem mem_S_st2 {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (st2 f lead i p).S) :
    m ∈ (st1 f i p).S
      ∨ ∃ b, m = Msg.block i b ∧ Action.send (Msg.block i b) i ∈ (propose f lead i (st1 f i p)).2 :=
  mem_S_propose hm

theorem mem_S_st3 {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (st3 f lead i p).S) :
    m ∈ (st2 f lead i p).S
      ∨ ∃ b, m = Msg.vote i b ∧ Action.send (Msg.vote i b) i ∈ (voteProposal f lead i (st2 f lead i p)).2 :=
  mem_S_voteProposal hm

theorem mem_S_st4 {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (st4 f Δ lead i p).S) :
    m ∈ (st3 f lead i p).S
      ∨ ∃ v, m = Msg.nullify i v ∧ Action.send (Msg.nullify i v) i ∈ (nullifyTimeout Δ i (st3 f lead i p)).2 :=
  mem_S_nullifyTimeout hm

theorem mem_S_st5 {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (st5 f Δ lead i p).S) :
    m ∈ (st4 f Δ lead i p).S
      ∨ ∃ v, m = Msg.nullify i v ∧ Action.send (Msg.nullify i v) i ∈ (nullifyNoProgress f i (st4 f Δ lead i p)).2 :=
  mem_S_nullifyNoProgress hm

/-- 13〜14 行の後の S にある自分の nullify は、前からあったか 13〜14 行で送った。 -/
theorem mem_S_st4_nullify {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    {w : View} (hm : Msg.nullify i w ∈ (st4 f Δ lead i p).S) :
    Msg.nullify i w ∈ p.S
      ∨ Action.send (Msg.nullify i w) i ∈ (nullifyTimeout Δ i (st3 f lead i p)).2 := by
  rcases mem_S_st4 hm with hm | ⟨v', hv', hs⟩
  · rcases mem_S_st3 hm with hm | ⟨_, hb, _⟩
    · rcases mem_S_st2 hm with hm | ⟨_, hb, _⟩
      · rcases mem_S_st1 hm with hm | ⟨_, hb, _⟩
        · exact Or.inl hm
        · cases hb
      · cases hb
    · cases hb
  · injection hv' with _ hw
    subst hw
    exact Or.inr hs

/-- 動作を終えた後の S にある message は、前からあったか、このスロットの転送以外の段で
    自分が送った自分の署名付きの message。 -/
theorem mem_S_stage_or_sent (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx)
    {m : Msg n Tx} (h : m ∈ (st5 f Δ lead i p).S) :
    m ∈ p.S ∨ (m.signer = some i ∧ ∃ j, Action.send m j ∈ innerActs f Δ lead i p) := by
  simp only [innerActs, List.mem_append]
  rcases mem_S_st5 h with h | ⟨v, rfl, hs⟩
  · rcases mem_S_st4 h with h | ⟨v, rfl, hs⟩
    · rcases mem_S_st3 h with h | ⟨b, rfl, hs⟩
      · rcases mem_S_st2 h with h | ⟨b, rfl, hs⟩
        · rcases mem_S_st1 h with h | ⟨b, rfl, _, j, hs⟩
          · exact Or.inl h
          · exact Or.inr ⟨rfl, j, by left; left; left; left; exact hs⟩
        · exact Or.inr ⟨rfl, i, by left; left; left; right; exact hs⟩
      · exact Or.inr ⟨rfl, i, by left; left; right; exact hs⟩
    · exact Or.inr ⟨rfl, i, by left; right; exact hs⟩
  · exact Or.inr ⟨rfl, i, by right; exact hs⟩

theorem mem_S_stage_or (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx)
    {m : Msg n Tx} (h : m ∈ (st5 f Δ lead i p).S) : m ∈ p.S ∨ m.signer = some i :=
  (mem_S_stage_or_sent f Δ lead i p h).imp_right And.left

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

/-- 5〜7 行が送るブロック。 -/
noncomputable def leaderBlock (f : Nat) (p : Processor n Tx) : Block Tx :=
  .node p.view (payload p.S (selectParent f p.S p.view)) (selectParent f p.S p.view)

theorem leaderBlock_view (f : Nat) (p : Processor n Tx) : (leaderBlock f p).view = p.view := rfl

theorem leaderBlock_ne_gen (f : Nat) (p : Processor n Tx) : leaderBlock f p ≠ .gen := by
  simp [leaderBlock]

theorem leaderBlock_parent (f : Nat) (p : Processor n Tx) :
    (leaderBlock f p).parent = some (selectParent f p.S p.view) := rfl

theorem send_propose_eq' {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    {m : Msg n Tx} {j : Fin n} (h : Action.send m j ∈ (propose f lead i p).2) :
    m = Msg.block i (leaderBlock f p) ∧ lead p.view = i ∧ p.proposed = false := by
  unfold propose at h
  split_ifs at h with hg
  · obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
    cases hm; exact ⟨rfl, hg.1, hg.2⟩
  · simp at h

/-- リーダーで未提案なら、5〜7 行はブロックを全員へ送る。 -/
theorem propose_fires {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (hl : lead p.view = i) (hp : p.proposed = false) (j : Fin n) :
    Action.send (Msg.block i (leaderBlock f p)) j ∈ (propose f lead i p).2 := by
  unfold propose
  rw [if_pos ⟨hl, hp⟩]
  exact mem_disseminate_snd.mpr ⟨j, rfl⟩

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

open Classical in
/-- lead(v) の view v の提案が S に b だけなら、9〜11 行は b について判定する。 -/
theorem voteProposal_eq_of_singleton {f : Nat} {lead : View → Fin n} {i : Fin n}
    {p : Processor n Tx} {b : Block Tx} (h : proposals lead p.S p.view = [b]) :
    voteProposal f lead i p
      = if ValidProposal f lead p.S p.view b ∧ p.notarised = none ∧ p.nullified = false then
          disseminate i p (.vote i b)
        else (p, []) := by
  unfold voteProposal; rw [h]

theorem disseminate_vote_notarised {i : Fin n} {p : Processor n Tx} {b : Block Tx}
    (hb : b.view = p.view) : (disseminate i p (Msg.vote i b)).1.notarised = some b := by
  rw [disseminate_fst]
  exact PreInv.foldl_send_vote_notarised hb (List.ne_nil_of_mem (List.mem_finRange i))

theorem send_nullifyTimeout_eq {Δ : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (nullifyTimeout Δ i p).2) :
    m = Msg.nullify i p.view ∧ p.nullified = false ∧ p.notarised = none
      ∧ (nullifyTimeout Δ i p).1.nullified = true ∧ p.timer = 2 * Δ := by
  unfold nullifyTimeout at h ⊢
  split_ifs at h ⊢ with hg
  · obtain ⟨_, hm⟩ := mem_disseminate_snd.mp h
    cases hm
    refine ⟨rfl, hg.2.1, hg.2.2, ?_, hg.1⟩
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

theorem send_advanceOnce_eq {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (advanceOnce f i p).2) :
    ∃ b, m = Msg.vote i b ∧ b.view = p.view ∧ MNotarised f p.S b ∧ p.notarised = none
      ∧ p.nullified = false ∧ (advanceOnce f i p).1.view.val = p.view.val + 1 := by
  rw [advanceOnce_eq] at h ⊢; split_ifs at h ⊢
  · simp at h
  · exact send_advanceM_eq h

/-- 登りで自分の票を出すなら、ある中間状態 q で 19〜21 行が出している。q は投票先の view に
    いて未投票で、S は登る前の S に、それより前の view のブロックへの自分の票を足したもの。 -/
theorem send_climb {f : Nat} {i : Fin n} {fuel : Nat} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (hL : LocalInv f i p) (h : Action.send m j ∈ (climb f i fuel p).2) :
    ∃ b q, m = Msg.vote i b ∧ LocalInv f i q ∧ q.view = b.view ∧ MNotarised f q.S b
      ∧ q.notarised = none ∧ q.nullified = false ∧ p.S ⊆ q.S ∧ p.view.val ≤ q.view.val
      ∧ (∀ m' ∈ q.S, m' ∈ p.S ∨ ∃ b', m' = Msg.vote i b' ∧ b'.view.val < q.view.val)
      ∧ b.view.val < (climb f i fuel p).1.view.val := by
  induction fuel generalizing p with
  | zero => simp [climb] at h
  | succ fuel ih =>
    by_cases hc : HasCert f p.S p.view
    · rw [climb_succ_of i hc] at h ⊢
      have hv := advanceOnce_view_succ (f := f) i hc
      have hle := view_le_climb f i fuel (advanceOnce f i p).1
      rcases List.mem_append.mp h with h | h
      · obtain ⟨b, rfl, hbv, hM, hnot, hnl, _⟩ := send_advanceOnce_eq h
        refine ⟨b, p, rfl, hL, hbv.symm, hM, hnot, hnl, Finset.Subset.refl _, le_refl _,
          fun m' hm' => Or.inl hm', ?_⟩
        show b.view.val < (climb f i fuel (advanceOnce f i p).1).1.view.val
        rw [hbv]; omega
      · obtain ⟨b, q, rfl, hLq, hqv, hM, hnot, hnl, hsub, hpq, hnew, hlt⟩ := ih hL.advanceOnce h
        refine ⟨b, q, rfl, hLq, hqv, hM, hnot, hnl, (S_subset_advanceOnce f i p).trans hsub,
          by omega, ?_, hlt⟩
        intro m' hm'
        rcases hnew m' hm' with hm' | hm'
        · rcases mem_S_advanceOnce hm' with hm' | ⟨b', rfl, hb', _⟩
          · exact Or.inl hm'
          · right
            refine ⟨b', rfl, ?_⟩
            rw [(mem_mNotarisedAt hb').1]; omega
        · exact Or.inr hm'
    · rw [climb_of_not i hc] at h; simp at h

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

theorem send_all_advanceM {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (advanceM f i p).2) (j' : Fin n) :
    Action.send m j' ∈ (advanceM f i p).2 := by
  unfold advanceM at h ⊢
  generalize mNotarisedAt f p.S p.view = l at h ⊢
  rcases l with _ | ⟨b, l⟩
  · simp at h
  · simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h ⊢
    split_ifs at h ⊢
    · obtain ⟨_, hmm⟩ := mem_disseminate_snd.mp h; cases hmm
      exact mem_disseminate_snd.mpr ⟨j', rfl⟩
    · simp at h

theorem send_all_advanceOnce {f : Nat} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx} {j : Fin n}
    (h : Action.send m j ∈ (advanceOnce f i p).2) (j' : Fin n) :
    Action.send m j' ∈ (advanceOnce f i p).2 := by
  rw [advanceOnce_eq] at h ⊢; split_ifs at h ⊢
  · simp at h
  · exact send_all_advanceM h j'

theorem send_all_climb {f : Nat} {i : Fin n} {fuel : Nat} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ (climb f i fuel p).2) (j' : Fin n) :
    Action.send m j' ∈ (climb f i fuel p).2 := by
  induction fuel generalizing p with
  | zero => simp [climb] at h
  | succ fuel ih =>
    by_cases hc : HasCert f p.S p.view
    · rw [climb_succ_of i hc] at h ⊢
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (send_all_advanceOnce h j')
      · exact List.mem_append_right _ (ih h)
    · rw [climb_of_not i hc] at h; simp at h

/-- 送る message は全員へ送る。 -/
theorem send_all {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    {j : Fin n} (h : Action.send m j ∈ Algo.step f Δ lead i p) (j' : Fin n) :
    Action.send m j' ∈ Algo.step f Δ lead i p := by
  rw [step_eq_stepPair, stepPair_snd] at h ⊢
  simp only [List.mem_append] at h ⊢
  rcases h with (((((h | h) | h) | h) | h) | h)
  · left; left; left; left; left
    exact send_all_climb h j'
  · left; left; left; left; right
    unfold propose at h ⊢
    split_ifs at h ⊢
    · obtain ⟨_, hmm⟩ := mem_disseminate_snd.mp h; cases hmm
      exact mem_disseminate_snd.mpr ⟨j', rfl⟩
    · simp at h
  · left; left; left; right
    unfold voteProposal at h ⊢
    generalize proposals lead (st2 f lead i p).S (st2 f lead i p).view = l at h ⊢
    rcases l with _ | ⟨b, _ | ⟨b', l⟩⟩
    · simp at h
    · simp only at h ⊢
      split_ifs at h ⊢
      · obtain ⟨_, hmm⟩ := mem_disseminate_snd.mp h; cases hmm
        exact mem_disseminate_snd.mpr ⟨j', rfl⟩
      · simp at h
    · simp at h
  · left; left; right
    unfold nullifyTimeout at h ⊢
    split_ifs at h ⊢
    · obtain ⟨_, hmm⟩ := mem_disseminate_snd.mp h; cases hmm
      exact mem_disseminate_snd.mpr ⟨j', rfl⟩
    · simp at h
  · left; right
    unfold nullifyNoProgress at h ⊢
    split_ifs at h ⊢
    · obtain ⟨_, hmm⟩ := mem_disseminate_snd.mp h; cases hmm
      exact mem_disseminate_snd.mpr ⟨j', rfl⟩
    · simp at h
  · right
    rw [forwardNew_eq] at h ⊢
    obtain ⟨m', hm', _, hmm⟩ := mem_disseminateAll_snd.mp h
    cases hmm
    exact mem_disseminateAll_snd.mpr ⟨_, hm', j', rfl⟩

/-! #### 票と nullify の出所 -/

theorem localInv_st1 {f : Nat} {i : Fin n} {p : Processor n Tx} (h : LocalInv f i p) :
    LocalInv f i (st1 f i p) := h.climb _

theorem localInv_st2 {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) : LocalInv f i (st2 f lead i p) := (localInv_st1 h).propose lead

theorem localInv_st3 {f : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) : LocalInv f i (st3 f lead i p) := (localInv_st2 h).voteProposal lead

theorem localInv_st4 {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) : LocalInv f i (st4 f Δ lead i p) :=
  (localInv_st3 (lead := lead) h).nullifyTimeout Δ

theorem localInv_st5 {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) : LocalInv f i (st5 f Δ lead i p) :=
  (localInv_st4 (Δ := Δ) (lead := lead) h).nullifyNoProgress

/-- 転送以外の段で自分の票を出す条件。 -/
theorem vote_emission_core {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) {b : Block Tx} {j : Fin n}
    (hv : Action.send (Msg.vote i b) j ∈ innerActs f Δ lead i p) :
    ∃ q : Processor n Tx, LocalInv f i q ∧ q.view = b.view
      ∧ q.notarised = none ∧ q.nullified = false ∧ p.S ⊆ q.S
      ∧ (∀ m ∈ q.S, m ∈ p.S ∨ m.signer = some i)
      ∧ (ValidProposal f lead q.S q.view b ∨ MNotarised f q.S b) := by
  have hst5 : ∀ m ∈ (st5 f Δ lead i p).S, m ∈ p.S ∨ m.signer = some i :=
    fun m hm => mem_S_stage_or f Δ lead i p hm
  simp only [innerActs, List.mem_append] at hv
  rcases hv with ((((hv | hv) | hv) | hv) | hv)
  · obtain ⟨b', q, hm, hLq, hqv, hM, hnot, hnl, hsub, _, hnew, _⟩ := send_climb h hv
    injection hm with _ hbb
    subst hbb
    refine ⟨q, hLq, hqv, hnot, hnl, hsub, ?_, Or.inr hM⟩
    intro m hm
    rcases hnew m hm with hm | ⟨b'', rfl, _⟩
    · exact Or.inl hm
    · exact Or.inr rfl
  · obtain ⟨_, hm⟩ := send_propose_eq hv; cases hm
  · obtain ⟨b', hm, hbv, hnot, hnl, hvp, _⟩ := send_voteProposal_eq hv
    injection hm with _ hbb
    subst hbb
    refine ⟨st2 f lead i p, localInv_st2 h, hbv.symm, hnot, hnl, S_subset_st2 f lead i p, ?_,
      Or.inl hvp⟩
    intro m hm
    exact hst5 m ((S_subset_voteProposal f lead i _).trans (S_st3_subset_st5 f Δ lead i p) hm)
  · obtain ⟨hm, _⟩ := send_nullifyTimeout_eq hv; cases hm
  · obtain ⟨hm, _⟩ := send_nullifyNoProgress_eq hv; cases hm

/-- 自分の票の出所: S にあった（転送）か、19〜21 行か 9〜11 行で、その段の入力 q は現在の
    view が b の view で、notarised = ⊥、nullified = false、S に M-notarisation か
    valid proposal がある。 -/
theorem vote_emission {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) {b : Block Tx} {j : Fin n}
    (hv : Action.send (Msg.vote i b) j ∈ Algo.step f Δ lead i p) :
    Msg.vote i b ∈ p.S ∨ ∃ q : Processor n Tx, LocalInv f i q ∧ q.view = b.view
      ∧ q.notarised = none ∧ q.nullified = false ∧ p.S ⊆ q.S
      ∧ (∀ m ∈ q.S, m ∈ p.S ∨ m.signer = some i)
      ∧ (ValidProposal f lead q.S q.view b ∨ MNotarised f q.S b) := by
  rw [step_eq_stepPair, stepPair_snd'] at hv
  rcases List.mem_append.mp hv with hv | hv
  · exact Or.inr (vote_emission_core h hv)
  · rcases mem_S_stage_or_sent f Δ lead i p (send_forwardNew_mem hv) with hm | ⟨_, j', hs⟩
    · exact Or.inl hm
    · exact Or.inr (vote_emission_core h hs)

/-- 自分の nullify(b.view) を出し、b への自分の票が S にあるか同じスロットで出すなら、
    nullify は 24〜28 行で、その段の入力 st4 には b 以外への進捗のなさの証拠がある。 -/
theorem nullify_after_vote {f Δ : Nat} {lead : View → Fin n} {i : Fin n} {p : Processor n Tx}
    (h : LocalInv f i p) {b : Block Tx} {j j' : Fin n}
    (hb : Msg.vote i b ∈ p.S ∨ Action.send (Msg.vote i b) j ∈ Algo.step f Δ lead i p)
    (hn : Action.send (Msg.nullify i b.view) j' ∈ Algo.step f Δ lead i p)
    (hno : Msg.nullify i b.view ∉ p.S) :
    LocalInv f i (st4 f Δ lead i p) ∧ (st4 f Δ lead i p).view = b.view
      ∧ (st4 f Δ lead i p).nullified = false ∧ Msg.vote i b ∈ (st4 f Δ lead i p).S
      ∧ NoProgress f (st4 f Δ lead i p).S b.view (some b) := by
  have h3 : LocalInv f i (st3 f lead i p) := localInv_st3 h
  have h4 : LocalInv f i (st4 f Δ lead i p) := localInv_st4 h
  -- 転送以外の段で票を出す場合の整理
  have hcore : ∀ {j : Fin n}, Action.send (Msg.vote i b) j ∈ innerActs f Δ lead i p →
      b.view.val < (st1 f i p).view.val
      ∨ (Msg.vote i b ∈ (st3 f lead i p).S ∧ (st3 f lead i p).notarised = some b) := by
    intro j hb
    simp only [innerActs, List.mem_append] at hb
    rcases hb with ((((hb | hb) | hb) | hb) | hb)
    · obtain ⟨b', _, hm, _, _, _, _, _, _, _, _, hlt⟩ := send_climb h hb
      injection hm with _ hbb
      subst hbb
      exact Or.inl hlt
    · obtain ⟨_, hm⟩ := send_propose_eq hb; cases hm
    · obtain ⟨b', hm, _, _, _, _, hnot⟩ := send_voteProposal_eq hb
      injection hm with _ hbb
      subst hbb
      exact Or.inr ⟨mem_S_of_send_voteProposal hb, hnot⟩
    · obtain ⟨hm, _⟩ := send_nullifyTimeout_eq hb; cases hm
    · obtain ⟨hm, _⟩ := send_nullifyNoProgress_eq hb; cases hm
  -- 票の出所
  have hvote : Msg.vote i b ∈ p.S
      ∨ b.view.val < (st1 f i p).view.val
      ∨ (Msg.vote i b ∈ (st3 f lead i p).S ∧ (st3 f lead i p).notarised = some b) := by
    rcases hb with hb | hb
    · exact Or.inl hb
    · rw [step_eq_stepPair, stepPair_snd'] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact Or.inr (hcore hb)
      · rcases mem_S_stage_or_sent f Δ lead i p (send_forwardNew_mem hb) with hm | ⟨_, _, hs⟩
        · exact Or.inl hm
        · exact Or.inr (hcore hs)
  -- nullify の出所（転送なら転送以外の段に遡る）
  obtain ⟨j'', hn'⟩ : ∃ j, Action.send (Msg.nullify i b.view) j ∈ innerActs f Δ lead i p := by
    rw [step_eq_stepPair, stepPair_snd'] at hn
    rcases List.mem_append.mp hn with hn | hn
    · exact ⟨j', hn⟩
    · rcases mem_S_stage_or_sent f Δ lead i p (send_forwardNew_mem hn) with hm | ⟨_, j'', hs⟩
      · exact absurd hm hno
      · exact ⟨j'', hs⟩
  simp only [innerActs, List.mem_append] at hn'
  rcases hn' with ((((hn | hn) | hn) | hn) | hn)
  · obtain ⟨_, _, hm, _⟩ := send_climb h hn; cases hm
  · obtain ⟨_, hm⟩ := send_propose_eq hn; cases hm
  · obtain ⟨_, hm, _⟩ := send_voteProposal_eq hn; cases hm
  · -- 13〜14 行: st3 で notarised = ⊥
    exfalso
    obtain ⟨hm, _, hnot3, _⟩ := send_nullifyTimeout_eq hn
    injection hm with _ hv3
    rcases hvote with hb | hlt | ⟨_, hnot⟩
    · have := ((h3.notar b (S_subset_st3 f lead i p hb)).2.resolve_left
        (by rw [hv3]; exact lt_irrefl _)).2
      rw [hnot3] at this; cases this
    · have h1 : b.view.val = (st1 f i p).view.val := by rw [hv3, st3_view]
      omega
    · rw [hnot3] at hnot; cases hnot
  · -- 24〜28 行
    obtain ⟨hm, hnl4, c₀, hc₀, hnp⟩ := send_nullifyNoProgress_eq hn
    injection hm with _ hv4
    have hvote4 : Msg.vote i b ∈ (st4 f Δ lead i p).S := by
      rcases hvote with hb | hlt | ⟨hb3, _⟩
      · exact S_subset_st4 f Δ lead i p hb
      · exfalso
        have h1 : b.view.val = (st1 f i p).view.val := by rw [hv4, st4_view]
        omega
      · exact S_st3_subset_st4 f Δ lead i p hb3
    have hnot4 := ((h4.notar b hvote4).2.resolve_left (by rw [hv4]; exact lt_irrefl _)).2
    rw [hc₀] at hnot4
    obtain rfl := Option.some.inj hnot4
    refine ⟨h4, hv4.symm, hnl4, hvote4, ?_⟩
    rw [hv4]; exact hnp

/-! #### 転送と反応のための補題 -/

/-- 転送はブロックを送らない。 -/
theorem not_block_mem_forwardMsgs {f : Nat} {p : Processor n Tx} {q : Fin n} {b : Block Tx} :
    Msg.block q b ∉ forwardMsgs f p := by
  simp only [forwardMsgs, List.mem_append, List.mem_flatMap, List.mem_filter, Finset.mem_toList,
    decide_eq_true_eq]
  rintro ((⟨v, _, _, q', hq⟩ | ⟨b', _, _, q', hq⟩) | ⟨_, h⟩)
  · cases hq
  · cases hq
  · simp at h

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

/-- 新しい取引は転送される。 -/
theorem mem_forwardMsgs_tx {f : Nat} {p : Processor n Tx} {tr : Tx} (h : Msg.tx tr ∈ p.S)
    (hnew : Msg.tx tr ∉ p.prevS) : Msg.tx tr ∈ forwardMsgs f p := by
  simp only [forwardMsgs, List.mem_append]
  right
  simp only [List.mem_filter, Finset.mem_toList]
  exact ⟨h, by simp [hnew]⟩

theorem send_mem_step_of_mem_forwardMsgs {f Δ : Nat} {lead : View → Fin n} {i : Fin n}
    {p : Processor n Tx} {m : Msg n Tx} (h : m ∈ forwardMsgs f (st5 f Δ lead i p)) (j : Fin n) :
    Action.send m j ∈ Algo.step f Δ lead i p := by
  rw [step_eq_stepPair, stepPair_snd']
  apply List.mem_append_right
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

theorem propose_timer (f : Nat) (lead : View → Fin n) (i : Fin n) (q : Processor n Tx) :
    (propose f lead i q).1.timer = q.timer := by
  unfold propose; split_ifs
  · exact disseminate_timer i _ _
  · rfl

theorem voteProposal_timer (f : Nat) (lead : View → Fin n) (i : Fin n) (q : Processor n Tx) :
    (voteProposal f lead i q).1.timer = q.timer := by
  unfold voteProposal
  rcases proposals lead q.S q.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · rfl
  · simp only; split_ifs
    · exact disseminate_timer i _ _
    · rfl
  · rfl

theorem nullifyTimeout_timer (Δ : Nat) (i : Fin n) (q : Processor n Tx) :
    (nullifyTimeout Δ i q).1.timer = q.timer := by
  unfold nullifyTimeout; split_ifs
  · exact disseminate_timer i _ _
  · rfl

theorem nullifyNoProgress_timer (f : Nat) (i : Fin n) (q : Processor n Tx) :
    (nullifyNoProgress f i q).1.timer = q.timer := by
  unfold nullifyNoProgress; split_ifs
  · exact disseminate_timer i _ _
  · rfl

theorem forwardNew_timer (f : Nat) (i : Fin n) (q : Processor n Tx) :
    (forwardNew f i q).1.timer = q.timer := by
  rw [forwardNew_eq]; exact disseminateAll_timer i q _

/-- prevS は動作で変わらない。 -/
theorem disseminate_prevS (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    (disseminate i p m).1.prevS = p.prevS := by
  rw [disseminate_fst]
  generalize List.finRange n = l
  induction l generalizing p with
  | nil => rfl
  | cons j l ih => rw [List.foldl_cons, ih, Processor.send_prevS]

theorem disseminateAll_prevS (i : Fin n) (p : Processor n Tx) (ms : List (Msg n Tx)) :
    (disseminateAll i p ms).1.prevS = p.prevS := by
  rw [disseminateAll_fst]
  induction ms generalizing p with
  | nil => rfl
  | cons m ms ih => rw [List.foldl_cons, ih, disseminate_prevS]

theorem forwardNew_prevS (f : Nat) (i : Fin n) (q : Processor n Tx) :
    (forwardNew f i q).1.prevS = q.prevS := by
  rw [forwardNew_eq]; exact disseminateAll_prevS i q _

theorem _root_.Minimmit.Processor.executeAll_prevS (i : Fin n) (p : Processor n Tx)
    (acts : List (Action n Tx)) : (p.executeAll i acts).prevS = p.prevS := by
  induction acts generalizing p with
  | nil => rfl
  | cons a acts ih =>
    show ((p.execute i a).executeAll i acts).prevS = p.prevS
    rw [ih]
    cases a with
    | send m j =>
      simp only [Processor.execute]
      split_ifs
      · rw [Processor.send_prevS]
      · rfl
    | progress => rfl

theorem st5_prevS (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st5 f Δ lead i p).prevS = p.prevS := by
  rw [← forwardNew_prevS f i, ← stepPair_fst, ← executeAll_step, Processor.executeAll_prevS]

/-- 5〜11 行は timer を変えない。 -/
theorem st3_timer (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st3 f lead i p).timer = (st1 f i p).timer := by
  simp only [st3, st2]; rw [voteProposal_timer, propose_timer]

/-- 5〜28 行と転送は timer を変えない。 -/
theorem stepPair_timer (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (stepPair f Δ lead i p).1.timer = (st1 f i p).timer := by
  rw [stepPair_fst, forwardNew_timer]
  simp only [st5, st4]
  rw [nullifyNoProgress_timer, nullifyTimeout_timer, st3_timer]

/-! #### SelectParent と valid proposal -/

theorem selectParent_mnotarised (f : Nat) (S : Finset (Msg n Tx)) (v : View) :
    MNotarised f S (selectParent f S v) := by
  unfold selectParent
  generalize hl : ((votedBlocks S).filter fun b => decide (b.view.val < v.val ∧ MNotarised f S b)).argmax
    (fun b => b.view.val) = o
  cases o with
  | none => exact Or.inl rfl
  | some b =>
    have hb := List.argmax_mem (Option.mem_def.mpr hl)
    simp only [List.mem_filter, decide_eq_true_eq] at hb
    exact hb.2.2

theorem selectParent_view_lt (f : Nat) (S : Finset (Msg n Tx)) {v : View} (hv : 1 ≤ v.val) :
    (selectParent f S v).view.val < v.val := by
  unfold selectParent
  generalize hl : ((votedBlocks S).filter fun b => decide (b.view.val < v.val ∧ MNotarised f S b)).argmax
    (fun b => b.view.val) = o
  cases o with
  | none => exact hv
  | some b =>
    have hb := List.argmax_mem (Option.mem_def.mpr hl)
    simp only [List.mem_filter, decide_eq_true_eq] at hb
    exact hb.2.1

/-- SelectParent は、M-notarisation を持つ v 未満の view のブロックのうち view 最大のものを選ぶ。 -/
theorem selectParent_max (f : Nat) (S : Finset (Msg n Tx)) (v : View) {b : Block Tx}
    (hb : b ∈ votedBlocks S) (hlt : b.view.val < v.val) (hM : MNotarised f S b) :
    b.view.val ≤ (selectParent f S v).view.val := by
  unfold selectParent
  have hmem : b ∈ (votedBlocks S).filter
      (fun b => decide (b.view.val < v.val ∧ MNotarised f S b)) := by
    simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hb, hlt, hM⟩
  generalize hl : ((votedBlocks S).filter fun b => decide (b.view.val < v.val ∧ MNotarised f S b)).argmax
    (fun b => b.view.val) = o at hmem
  cases o with
  | none =>
    rw [List.argmax_eq_none] at hl
    rw [hl] at hmem
    simp at hmem
  | some m =>
    show b.view.val ≤ m.view.val
    exact List.le_of_mem_argmax (f := fun b : Block Tx => b.view.val) hmem (Option.mem_def.mpr hl)

/-- lead(v) の署名付きの view v のブロックが S に b しかなければ、`proposals` は [b]。 -/
theorem proposals_eq_singleton {lead : View → Fin n} {S : Finset (Msg n Tx)} {v : View}
    {b : Block Tx} (hb : Msg.block (lead v) b ∈ S) (hbv : b.view = v)
    (huniq : ∀ b', b'.view = v → Msg.block (lead v) b' ∈ S → b' = b) :
    proposals lead S v = [b] := by
  have hmem : ∀ b', b' ∈ proposals lead S v ↔ b' = b := by
    intro b'
    simp only [proposals, List.mem_dedup, List.mem_filterMap, Finset.mem_toList]
    constructor
    · rintro ⟨m, hm, hmb⟩
      cases m with
      | block q b'' =>
        simp only at hmb
        split_ifs at hmb with hq
        obtain rfl := Option.some.inj hmb
        exact huniq _ hq.2 (hq.1 ▸ hm)
      | vote q b'' => simp at hmb
      | nullify q w => simp at hmb
      | tx tr => simp at hmb
    · intro hb'
      rw [hb']
      exact ⟨Msg.block (lead v) b, hb, by simp [hbv]⟩
  have hnd : (proposals lead S v).Nodup := List.nodup_dedup _
  rcases hl : proposals lead S v with _ | ⟨x, _ | ⟨y, l⟩⟩
  · exact absurd ((hmem b).mpr rfl) (by rw [hl]; simp)
  · rw [(hmem x).mp (by rw [hl]; simp)]
  · exfalso
    have hx := (hmem x).mp (by rw [hl]; simp)
    have hy := (hmem y).mp (by rw [hl]; simp)
    rw [hl] at hnd
    simp [hx, hy] at hnd

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

theorem S_st5_subset_stepPair (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    (st5 f Δ lead i p).S ⊆ (stepPair f Δ lead i p).1.S := by
  rw [stepPair_fst, forwardNew_S]

end Algo

end Minimmit
