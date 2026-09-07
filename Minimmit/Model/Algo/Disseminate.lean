import Minimmit.Model.Algo.Basic
import Minimmit.Model.Transition.Execute
import Minimmit.Model.Certificate.Mono

/-!
# disseminate と disseminateAll の補題

全員への送信の、返す動作列と局所状態。
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
    (h : p.canSend i m) :
    p.executeAll i (disseminate i p m).2 = (disseminate i p m).1 := by
  rw [disseminate_snd, disseminate_fst]
  suffices key : ∀ (l : List (Fin n)) (p : Processor n Tx), p.canSend i m →
      p.executeAll i (l.map (Action.send m)) = l.foldl (fun p j => p.send i m j) p by
    exact key _ _ h
  intro l
  induction l with
  | nil => intros; rfl
  | cons j l ih =>
    intro p h
    simp only [List.map_cons, Processor.executeAll_cons, List.foldl_cons, Processor.execute,
      if_pos h]
    exact ih _ (Processor.canSend_mono (Processor.S_subset_send i p m j) h)

/-- ガードを通る message の disseminate の各 send は、その時点のガードを通る。 -/
theorem guardOK_disseminate {i : Fin n} {p : Processor n Tx} {m : Msg n Tx} (h : p.canSend i m) :
    Processor.GuardOK i p (disseminate i p m).2 := by
  rw [disseminate_snd]
  suffices key : ∀ (l : List (Fin n)) (p : Processor n Tx), p.canSend i m →
      Processor.GuardOK i p (l.map (Action.send m)) by
    exact key _ _ h
  intro l
  induction l with
  | nil => intros; trivial
  | cons j l ih =>
    intro p h
    simp only [List.map_cons]
    exact Processor.GuardOK.send_cons h
      (ih _ (Processor.canSend_mono (Processor.S_subset_send i p m j) h))

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
    (h : ∀ m ∈ ms, p.canSend i m) :
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
      Processor.canSend_mono (S_subset_disseminate_fst i p m) (h m' (List.mem_cons_of_mem _ hm'))

theorem guardOK_disseminateAll {i : Fin n} {p : Processor n Tx} {ms : List (Msg n Tx)}
    (h : ∀ m ∈ ms, p.canSend i m) : Processor.GuardOK i p (disseminateAll i p ms).2 := by
  rw [disseminateAll_snd]
  revert h
  induction ms generalizing p with
  | nil => intro _; trivial
  | cons m ms ih =>
    intro h
    simp only [List.flatMap_cons]
    rw [← disseminate_snd i p m]
    refine Processor.GuardOK.append (guardOK_disseminate (h m (List.mem_cons_self ..))) ?_
    rw [executeAll_disseminate (h m (List.mem_cons_self ..))]
    exact ih fun m' hm' =>
      Processor.canSend_mono (S_subset_disseminate_fst i p m) (h m' (List.mem_cons_of_mem _ hm'))

end Algo

end Minimmit
