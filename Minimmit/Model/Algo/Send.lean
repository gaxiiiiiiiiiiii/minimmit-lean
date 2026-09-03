import Minimmit.Model.Algo.Climb

/-!
# 各段の S の中身と送信

各段の後の S にある message の出所、各段が送る message とそのときの条件、
票と nullify の出所（`vote_emission`・`nullify_after_vote`）。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

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

end Algo

end Minimmit
