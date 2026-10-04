import Minimmit.Model.Algo.LocalInv

/-!
# `climb`（16〜21 行）の補題

通過した view の証明書は `climb` の前の S にある、v 未満の各 view の証明書があれば v 以上に達する、
`climb` の後に現在の view の証明書は残らない、`climb` の後の状態 st1 の性質。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

/-! #### 証明書 -/

/-- 証明書のある view は、S にあるメッセージの view を超えない。 -/
theorem hasCert_le_maxView {f : Nat} {S : Finset (Msg n Tx)} {v : View} (h : HasCert f S v) :
    v.val ≤ maxView S := by
  rcases h with h | h
  · exact view_le_maxView_of_nullified h
  · obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ h
    exact view_le_maxView_of_mem_mNotarisedAt hb

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
    (hnew : ∀ m ∈ S', m ∈ S ∨ ∃ b, m = Msg.vote i b ∧ b.view.val < w.val)
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
      refine hb'.2.trans (Finset.card_le_card fun q' hq' => ?_)
      rw [mem_voters] at hq' ⊢
      exact hvote q' hq'
    apply List.ne_nil_of_mem (a := b)
    rw [← hb'.1]
    exact mem_mNotarisedAt_of (mem_votedBlocks (hvote q hq)) hM

/-! #### 16〜21 行の繰り返し -/

/-- view は `climb` で減らない。 -/
theorem view_le_climb (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.view.val ≤ (climb f i p).1.view.val := by
  refine climb_induction f i ?_ ?_ ?_ p
  · intro p hN ih
    rw [climb_of_nullified i hN]
    exact (Nat.le_succ _).trans ih
  · intro p hN hM ih
    rw [climb_of_mnotarised i hN hM]
    dsimp only
    have hv := ite_vote_progress_view i p ((mNotarisedAt f p.S p.view).head hM)
    omega
  · intro p hN hM
    rw [climb_of_not i fun h => h.elim hN hM]

/-- 現在の view の証明書があれば、`climb` は view を進める。 -/
theorem view_lt_climb_of_hasCert {f : Nat} (i : Fin n) {p : Processor n Tx}
    (hc : HasCert f p.S p.view) : p.view.val < (climb f i p).1.view.val := by
  by_cases hN : Nullified f p.S p.view
  · rw [climb_of_nullified i hN]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (view_le_climb f i p.progress)
  · have hM := hc.resolve_left hN
    rw [climb_of_mnotarised i hN hM]
    dsimp only
    have hv := ite_vote_progress_view i p ((mNotarisedAt f p.S p.view).head hM)
    have hle := view_le_climb f i (if p.notarised = none ∧ p.nullified = false
      then disseminate i p (.vote i ((mNotarisedAt f p.S p.view).head hM)) else (p, [])).1.progress
    omega

/-- view が変わらなければ、`climb` は何もしていない。 -/
theorem climb_eq_of_view {f : Nat} {i : Fin n} {p : Processor n Tx}
    (h : (climb f i p).1.view = p.view) : climb f i p = (p, []) := by
  by_cases hc : HasCert f p.S p.view
  · exfalso
    have := view_lt_climb_of_hasCert i hc
    rw [h] at this
    exact lt_irrefl _ this
  · exact climb_of_not i hc

/-- `climb` の後は、現在の view の証明書がない。 -/
theorem climb_quiescent (f : Nat) (i : Fin n) (p : Processor n Tx) :
    ¬ HasCert f (climb f i p).1.S (climb f i p).1.view := by
  refine climb_induction f i ?_ ?_ ?_ p
  · intro p hN ih
    rw [climb_of_nullified i hN]
    exact ih
  · intro p hN hM ih
    rw [climb_of_mnotarised i hN hM]
    dsimp only
    exact ih
  · intro p hN hM
    rw [climb_of_not i fun h => h.elim hN hM]
    exact fun h => h.elim hN hM

/-- `climb` の後の S にあるメッセージは、前からあったか、`climb` で出した自分の票。票の view は
    `climb` の後の view より小さい。 -/
theorem mem_S_climb {f : Nat} {i : Fin n} {q : Processor n Tx} {m : Msg n Tx}
    (hm : m ∈ (climb f i q).1.S) :
    m ∈ q.S ∨ ∃ b, m = Msg.vote i b ∧ b.view.val < (climb f i q).1.view.val
      ∧ ∃ j, Action.send (Msg.vote i b) j ∈ (climb f i q).2 := by
  revert hm
  refine climb_induction f i ?_ ?_ ?_ q
  · intro q hN ih hm
    rw [climb_of_nullified i hN] at hm ⊢
    rcases ih hm with hm | ⟨b, rfl, hb, j, hj⟩
    · exact Or.inl hm
    · exact Or.inr ⟨b, rfl, hb, j, List.mem_cons_of_mem _ hj⟩
  · intro q hN hM ih hm
    rw [climb_of_mnotarised i hN hM] at hm ⊢
    dsimp only at hm ⊢
    have hb₀ := List.head_mem hM
    generalize (mNotarisedAt f q.S q.view).head hM = b₀ at ih hm hb₀ ⊢
    have hv := ite_vote_progress_view i q b₀
    have hle := view_le_climb f i (if q.notarised = none ∧ q.nullified = false
      then disseminate i q (.vote i b₀) else (q, [])).1.progress
    rcases ih hm with hm | ⟨b, rfl, hb, j, hj⟩
    · rcases mem_S_ite_vote_or hm with hm | ⟨rfl, hs⟩
      · exact Or.inl hm
      · right
        refine ⟨b₀, rfl, ?_, i, List.mem_append_left _ hs⟩
        rw [(mem_mNotarisedAt hb₀).1]; omega
    · exact Or.inr ⟨b, rfl, hb, j, List.mem_append_right _ (List.mem_cons_of_mem _ hj)⟩
  · intro q hN hM hm
    rw [climb_of_not i fun h => h.elim hN hM] at hm ⊢
    exact Or.inl hm

/-- `climb` で通過した view の証明書は、`climb` の前の S にある。 -/
theorem climb_certs (f : Nat) (i : Fin n) (p : Processor n Tx) :
    ∀ w : View, p.view.val ≤ w.val → w.val < (climb f i p).1.view.val → HasCert f p.S w := by
  refine climb_induction f i ?_ ?_ ?_ p
  · intro p hN ih w h1 h2
    rw [climb_of_nullified i hN] at h2
    by_cases hw : w.val = p.view.val
    · rw [View.val_injective hw]; exact Or.inl hN
    · exact ih w (by show p.view.val + 1 ≤ w.val; omega) h2
  · intro p hN hM ih w h1 h2
    rw [climb_of_mnotarised i hN hM] at h2
    dsimp only at ih h2
    have hb₀ := List.head_mem hM
    generalize (mNotarisedAt f p.S p.view).head hM = b₀ at ih h2 hb₀
    by_cases hw : w.val = p.view.val
    · rw [View.val_injective hw]; exact Or.inr hM
    · have hv := ite_vote_progress_view i p b₀
      have hw' := ih w (by omega) h2
      refine hasCert_of_votes_lt (i := i) (S := p.S) ?_ hw'
      intro m hm
      rcases mem_S_ite_vote_or hm with hm | ⟨rfl, _⟩
      · exact Or.inl hm
      · right
        refine ⟨b₀, rfl, ?_⟩
        rw [(mem_mNotarisedAt hb₀).1]; omega
  · intro p hN hM w h1 h2
    rw [climb_of_not i fun h => h.elim hN hM] at h2
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

/-- v 未満の各 view の証明書があれば、`climb` は v 以上に達する。 -/
theorem climb_reaches (f : Nat) (i : Fin n) (p : Processor n Tx) (v : View)
    (hcerts : ∀ w : View, p.view.val ≤ w.val → w.val < v.val → HasCert f p.S w) :
    v.val ≤ (climb f i p).1.view.val := by
  revert hcerts
  refine climb_induction f i ?_ ?_ ?_ p
  · intro p hN ih hcerts
    rw [climb_of_nullified i hN]
    exact ih fun w h1 h2 => hcerts w (Nat.le_of_succ_le h1) h2
  · intro p hN hM ih hcerts
    rw [climb_of_mnotarised i hN hM]
    dsimp only at ih ⊢
    generalize (mNotarisedAt f p.S p.view).head hM = b₀ at ih ⊢
    have hv := ite_vote_progress_view i p b₀
    apply ih
    intro w h1 h2
    exact (hcerts w (by omega) h2).mono (S_subset_ite_vote i p b₀)
  · intro p hN hM hcerts
    rw [climb_of_not i fun h => h.elim hN hM]
    by_contra hlt
    exact (hcerts p.view (le_refl _) (not_le.mp hlt)).elim hN hM

/-- `climb` で view w を通過する中間状態 q: q の S は `climb` の前の S に、w 未満の view への自分の
    票を足したもので、w の証明書を持つ。q からの `climb` は、p からの `climb` の残りの部分。 -/
theorem climb_pass {f : Nat} {i : Fin n} {p : Processor n Tx} (hL : LocalInv f i p)
    {w : View} (h1 : p.view.val ≤ w.val) (h2 : w.val < (climb f i p).1.view.val) :
    ∃ q, LocalInv f i q ∧ q.view = w ∧ p.S ⊆ q.S ∧ HasCert f q.S w
      ∧ (∀ m ∈ q.S, m ∈ p.S ∨ ∃ b', m = Msg.vote i b' ∧ b'.view.val < w.val)
      ∧ (climb f i q).1 = (climb f i p).1
      ∧ ∀ a ∈ (climb f i q).2, a ∈ (climb f i p).2 := by
  revert hL h1 h2
  refine climb_induction f i ?_ ?_ ?_ p
  · intro p hN ih hL h1 h2
    by_cases hw : w.val = p.view.val
    · refine ⟨p, hL, (View.val_injective hw).symm, Finset.Subset.refl _, ?_,
        fun m hm => Or.inl hm, rfl, fun a ha => ha⟩
      rw [View.val_injective hw]; exact Or.inl hN
    · rw [climb_of_nullified i hN] at h2 ⊢
      obtain ⟨q, hLq, hqv, hsub, hcert, hnew, hq1, hq2⟩ :=
        ih hL.progress (by show p.view.val + 1 ≤ w.val; omega) h2
      exact ⟨q, hLq, hqv, hsub, hcert, hnew, hq1, fun a ha => List.mem_cons_of_mem _ (hq2 a ha)⟩
  · intro p hN hM ih hL h1 h2
    by_cases hw : w.val = p.view.val
    · refine ⟨p, hL, (View.val_injective hw).symm, Finset.Subset.refl _, ?_,
        fun m hm => Or.inl hm, rfl, fun a ha => ha⟩
      rw [View.val_injective hw]; exact Or.inr hM
    · rw [climb_of_mnotarised i hN hM] at h2 ⊢
      dsimp only at ih h2 ⊢
      have hb₀ := List.head_mem hM
      generalize (mNotarisedAt f p.S p.view).head hM = b₀ at ih h2 hb₀ ⊢
      have hv := ite_vote_progress_view i p b₀
      obtain ⟨q, hLq, hqv, hsub, hcert, hnew, hq1, hq2⟩ :=
        ih (hL.ite_vote hb₀).progress (by omega) h2
      refine ⟨q, hLq, hqv, (S_subset_ite_vote i p b₀).trans hsub, hcert, ?_, hq1,
        fun a ha => List.mem_append_right _ (List.mem_cons_of_mem _ (hq2 a ha))⟩
      intro m hm
      rcases hnew m hm with hm | hm
      · rcases mem_S_ite_vote_or hm with hm | ⟨rfl, _⟩
        · exact Or.inl hm
        · right
          refine ⟨b₀, rfl, ?_⟩
          rw [(mem_mNotarisedAt hb₀).1]; omega
      · exact Or.inr hm
  · intro p hN hM _ h1 h2
    rw [climb_of_not i fun h => h.elim hN hM] at h2
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

/-- nullification がなく M-notarisation があり、未投票で nullify も出していなければ、
    19〜21 行は M-notarisation のあるブロックに投票する。 -/
theorem climb_vote_of {f : Nat} (i : Fin n) {q : Processor n Tx}
    (hN : ¬ Nullified f q.S q.view) (hM : mNotarisedAt f q.S q.view ≠ [])
    (hn : q.notarised = none) (hnl : q.nullified = false) :
    ∃ b ∈ mNotarisedAt f q.S q.view, Action.send (Msg.vote i b) i ∈ (climb f i q).2 := by
  rw [climb_of_mnotarised i hN hM]
  dsimp only
  rw [if_pos ⟨hn, hnl⟩]
  exact ⟨_, List.head_mem hM, List.mem_append_left _ (mem_disseminate_snd.mpr ⟨i, rfl⟩)⟩

/-- `climb` は何もしないか、timer を 0 にし proposed を false にする。 -/
theorem climb_eq_or (f : Nat) (i : Fin n) (p : Processor n Tx) :
    climb f i p = (p, [])
      ∨ ((climb f i p).1.timer = 0 ∧ (climb f i p).1.proposed = false) := by
  refine climb_induction f i ?_ ?_ ?_ p
  · intro p hN ih
    right
    rw [climb_of_nullified i hN]
    rcases ih with h | h
    · show (climb f i p.progress).1.timer = 0 ∧ (climb f i p.progress).1.proposed = false
      rw [h]; exact ⟨rfl, rfl⟩
    · exact h
  · intro p hN hM ih
    right
    rw [climb_of_mnotarised i hN hM]
    dsimp only
    rcases ih with h | h
    · rw [h]; exact ⟨rfl, rfl⟩
    · exact h
  · intro p hN hM
    exact Or.inl (climb_of_not i fun h => h.elim hN hM)

/-! #### st1: `climb` の後の状態 -/

theorem st1_eq_or (f : Nat) (i : Fin n) (p : Processor n Tx) :
    st1 f i p = p ∨ ((st1 f i p).timer = 0 ∧ (st1 f i p).proposed = false) := by
  rcases climb_eq_or f i p with h | h
  · left; show (climb f i p).1 = p; rw [h]
  · exact Or.inr h

theorem view_le_st1 (f : Nat) (i : Fin n) (p : Processor n Tx) :
    p.view.val ≤ (st1 f i p).view.val :=
  view_le_climb f i p

/-- view が変わらなければ、16〜21 行は何もしていない。 -/
theorem st1_eq_of_view {f : Nat} {i : Fin n} {p : Processor n Tx}
    (h : (st1 f i p).view = p.view) : st1 f i p = p := by
  show (climb f i p).1 = p
  rw [climb_eq_of_view h]

theorem st1_certs {f : Nat} {i : Fin n} {p : Processor n Tx} {w : View} (h1 : p.view.val ≤ w.val)
    (h2 : w.val < (st1 f i p).view.val) : HasCert f p.S w :=
  climb_certs f i p w h1 h2

theorem view_lt_st1_of_hasCert {f : Nat} (i : Fin n) {p : Processor n Tx}
    (hc : HasCert f p.S p.view) : p.view.val < (st1 f i p).view.val :=
  view_lt_climb_of_hasCert i hc

/-- v 未満の各 view の証明書があれば、`climb` は v 以上に達する。 -/
theorem st1_reaches {f : Nat} (i : Fin n) {p : Processor n Tx} {v : View}
    (hcerts : ∀ w : View, p.view.val ≤ w.val → w.val < v.val → HasCert f p.S w) :
    v.val ≤ (st1 f i p).view.val :=
  climb_reaches f i p v hcerts

/-- `climb` の後は、現在の view の証明書がない。 -/
theorem st1_quiescent (f : Nat) (i : Fin n) (p : Processor n Tx) :
    ¬ HasCert f (st1 f i p).S (st1 f i p).view :=
  climb_quiescent f i p

/-- 部分を進めても S は減らない。 -/
theorem S_subset_st1 (f : Nat) (i : Fin n) (p : Processor n Tx) : p.S ⊆ (st1 f i p).S :=
  S_subset_climb f i p

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

end Algo

end Minimmit
