import Minimmit.Model.Algo.Send

/-!
# 転送と反応、SelectParent の補題

新しい証明書の転送、timer と prevS の推移、13〜14 行と 24〜28 行の発火、
SelectParent と valid proposal。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

/-! #### 転送と反応のための補題 -/

/-- 転送はブロックを送らない。 -/
theorem not_propose_mem_forwardMsgs {f : Nat} {p : Processor n Tx} {b : Block n Tx} :
    Msg.propose b ∉ forwardMsgs f p := by
  simp only [forwardMsgs, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_map,
    Finset.mem_toList, decide_eq_true_eq]
  rintro ((⟨v, _, q', _, hq⟩ | ⟨b', _, q', _, hq⟩) | ⟨_, h⟩)
  · cases hq
  · cases hq
  · simp at h

/-- 新しい nullification の、番号の小さい順 2f + 1 人の nullify は転送される。 -/
theorem mem_forwardMsgs_nullify {f : Nat} {p : Processor n Tx} {q : Fin n} {v : View}
    (h1 : Nullified f p.S v) (h2 : ¬ Nullified f p.prevS v) (hq : q ∈ leastNullifiers f p.S v) :
    Msg.nullify q v ∈ forwardMsgs f p := by
  have hm : Msg.nullify q v ∈ p.S := (Finset.mem_filter.mp (leastNullifiers_subset f _ _ hq)).2
  simp only [forwardMsgs, List.mem_append]
  left; left
  simp only [List.mem_flatMap, List.mem_filter, List.mem_map, Finset.mem_toList,
    decide_eq_true_eq]
  exact ⟨v, ⟨mem_nullifyViews hm, h1, h2⟩, q, hq, rfl⟩

/-- 新しい M-notarisation の、番号の小さい順 2f + 1 人の票は転送される。 -/
theorem mem_forwardMsgs_vote {f : Nat} {p : Processor n Tx} {q : Fin n} {b : Block n Tx}
    (h1 : MNotarised f p.S b) (h2 : ¬ MNotarised f p.prevS b) (hq : q ∈ leastVoters f p.S b) :
    Msg.vote q b ∈ forwardMsgs f p := by
  have hm : Msg.vote q b ∈ p.S := (Finset.mem_filter.mp (leastVoters_subset f _ _ hq)).2
  simp only [forwardMsgs, List.mem_append]
  left; right
  simp only [List.mem_flatMap, List.mem_filter, List.mem_map, Finset.mem_toList,
    decide_eq_true_eq]
  exact ⟨b, ⟨mem_votedBlocks hm, h1, h2⟩, q, hq, rfl⟩

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
  generalize hl :
      ((votedBlocks S).filter fun b => decide (b.view.val < v.val ∧ MNotarised f S b)).argmax
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
  generalize hl :
      ((votedBlocks S).filter fun b => decide (b.view.val < v.val ∧ MNotarised f S b)).argmax
    (fun b => b.view.val) = o
  cases o with
  | none => exact hv
  | some b =>
    have hb := List.argmax_mem (Option.mem_def.mpr hl)
    simp only [List.mem_filter, decide_eq_true_eq] at hb
    exact hb.2.1

/-- SelectParent は、M-notarisation を持つ v 未満の view のブロックのうち view 最大のものを選ぶ。 -/
theorem selectParent_max (f : Nat) (S : Finset (Msg n Tx)) (v : View) {b : Block n Tx}
    (hb : b ∈ votedBlocks S) (hlt : b.view.val < v.val) (hM : MNotarised f S b) :
    b.view.val ≤ (selectParent f S v).view.val := by
  unfold selectParent
  have hmem : b ∈ (votedBlocks S).filter
      (fun b => decide (b.view.val < v.val ∧ MNotarised f S b)) := by
    simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hb, hlt, hM⟩
  generalize hl :
      ((votedBlocks S).filter fun b => decide (b.view.val < v.val ∧ MNotarised f S b)).argmax
    (fun b => b.view.val) = o at hmem
  cases o with
  | none =>
    rw [List.argmax_eq_none] at hl
    rw [hl] at hmem
    simp at hmem
  | some m =>
    show b.view.val ≤ m.view.val
    exact List.le_of_mem_argmax (f := fun b : Block n Tx => b.view.val) hmem (Option.mem_def.mpr hl)

/-- lead(v) の署名付きの view v のブロックを S が b 以外に含まなければ、`proposals` は [b]。 -/
theorem proposals_eq_singleton {lead : View → Fin n} {S : Finset (Msg n Tx)} {v : View}
    {b : Block n Tx} (hb : containsBlock S b) (hsig : b.signer = some (lead v)) (hbv : b.view = v)
    (huniq : ∀ b', b'.view = v → b'.signer = some (lead v) → containsBlock S b' → b' = b) :
    proposals lead S v = [b] := by
  have hmem : ∀ b', b' ∈ proposals lead S v ↔ b' = b := by
    intro b'
    constructor
    · intro h
      have hc := containsBlock_of_mem_proposals h
      simp only [proposals, List.mem_dedup, List.mem_filterMap, Finset.mem_toList] at h
      obtain ⟨m, hm, hmb⟩ := h
      cases hb' : m.block with
      | none => simp [hb'] at hmb
      | some b'' =>
        simp only [hb'] at hmb
        split_ifs at hmb with hq
        simp only [Option.some.injEq] at hmb; subst hmb
        exact huniq _ hq.2 hq.1 hc
    · rintro rfl
      obtain ⟨m, hm, hmb⟩ := hb
      simp only [proposals, List.mem_dedup, List.mem_filterMap, Finset.mem_toList]
      exact ⟨m, hm, by simp [hmb, hsig, hbv]⟩
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

theorem nullifyNoProgress_fires {f : Nat} {i : Fin n} {q : Processor n Tx} {c : Block n Tx}
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
