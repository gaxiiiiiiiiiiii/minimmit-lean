import Minimmit.Model.Algo.LocalInv

/-!
# 登り（16〜21 行の繰り返し）の補題

通過した view の証明書は登る前の S にある、証明書がある限り登る、燃料 maxView + 1 で止まる、
登りの後の状態 st1 の性質。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

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
  | propose q b' => simp at hmb
  | vote q b' => simp at hmb; subst hmb; exact ⟨q, hm⟩
  | nullify q v => simp at hmb
  | tx tr => simp at hmb

theorem mem_votedBlocks_of_mem_mNotarisedAt {f : Nat} {S : Finset (Msg n Tx)} {v : View}
    {b : Block Tx} (h : b ∈ mNotarisedAt f S v) : b ∈ votedBlocks S := by
  simp only [mNotarisedAt, List.mem_filter] at h
  exact h.1

theorem mem_mNotarisedAt_of {f : Nat} {S : Finset (Msg n Tx)} {b : Block Tx}
    (hb : b ∈ votedBlocks S)
    (hM : MNotarised f S b) : b ∈ mNotarisedAt f S b.view := by
  simp only [mNotarisedAt, List.mem_filter, decide_eq_true_eq]
  exact ⟨hb, trivial, hM⟩

omit [DecidableEq Tx] in
theorem view_le_maxView {S : Finset (Msg n Tx)} {m : Msg n Tx} (h : m ∈ S) :
    m.view.val ≤ maxView S :=
  Finset.le_sup (f := fun m => m.view.val) h

/-- 証明書のある view は、S にある message の view を超えない。 -/
theorem hasCert_le_maxView {f : Nat} {S : Finset (Msg n Tx)} {v : View} (h : HasCert f S v) :
    v.val ≤ maxView S := by
  rcases h with h | h
  · obtain ⟨q, hq⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos _) h)
    exact view_le_maxView (mem_nullifiers.mp hq)
  · obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨q, hq⟩ := exists_vote_of_mem_votedBlocks (mem_votedBlocks_of_mem_mNotarisedAt hb)
    have h1 : b.view.val ≤ maxView S := view_le_maxView hq
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
  · exact view_le_maxView hm
  · obtain ⟨q, hq⟩ := exists_vote_of_mem_votedBlocks (mem_votedBlocks_of_mem_mNotarisedAt hb)
    have h1 : b.view.val ≤ maxView p.S := view_le_maxView hq
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
        refine hasCert_of_votes_lt (i := i) (S := p.S) ?_ hw'
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

/-- 登りで view w を通過する中間状態 q: q の S は登る前の S に、w 未満の view への自分の票を
    足したもので、w の証明書を持つ。 -/
theorem climb_pass {f : Nat} {i : Fin n} {fuel : Nat} {p : Processor n Tx} (hL : LocalInv f i p)
    {w : View} (h1 : p.view.val ≤ w.val) (h2 : w.val < (climb f i fuel p).1.view.val) :
    ∃ q, LocalInv f i q ∧ q.view = w ∧ p.S ⊆ q.S ∧ HasCert f q.S w
      ∧ (∀ m ∈ q.S, m ∈ p.S ∨ ∃ b', m = Msg.vote i b' ∧ b'.view.val < w.val)
      ∧ (advanceOnce f i q).1.S ⊆ (climb f i fuel p).1.S
      ∧ (∀ m j, Action.send m j ∈ (advanceOnce f i q).2
        → Action.send m j ∈ (climb f i fuel p).2) := by
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

/-- 証明書があって進んだ後の timer・proposed・notarised・nullified -/
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

end Algo

end Minimmit
