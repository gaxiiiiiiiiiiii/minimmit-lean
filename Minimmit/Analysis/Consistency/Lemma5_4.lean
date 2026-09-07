import Minimmit.Analysis.Consistency.Lemma5_3

/-!
# Lemma 5.4（Consistency）

M-notarisation を受けたブロックの親と祖先も M-notarisation を受けることから、
L-notarisation を受けた 2 つのブロックは一方が他方の祖先。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

omit [DecidableEq Tx] in
theorem receivesM_of_receivesL (hn : 5 * f + 1 ≤ n) {b : Block n Tx} (hL : ReceivesL f instrs b) :
    ReceivesM f instrs b :=
  hL.imp_right fun h => le_trans (by omega) h

theorem one_le_view_of_receivesL (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs) {b : Block n Tx}
    (hL : ReceivesL f instrs b) (hg : b ≠ .gen) : 1 ≤ b.view.val := by
  rcases hL with rfl | hL
  · exact absurd rfl hg
  · obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb (lt_of_lt_of_le (by omega) hL)
    exact one_le_view_of_sends hinit hh hqc (mem_voteSenders.mp hq)

/-- 正直者の各段の S にある message は、その正直者が実行上で送ったものか、そのスロットの
    自分の送信。 -/
theorem sends_of_mem_S_st5 (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {q : Fin n}
    (hqc : Correct s₀ instrs q) {t : Nat} {m : Msg n Tx}
    (hm : m ∈ (Algo.st5 f Δ lead q ((State.run s₀ instrs t).procs q)).S) {w : Fin n}
    (hw : m.signer = some w) (hg : m ≠ .vote w .gen) : Sends instrs w m := by
  rcases Algo.mem_S_stage_or_sent f Δ lead q _ hm with hm' | ⟨hs, j, hj⟩
  · exact sends_of_mem_S hinit hm' hw hg
  · rw [hs] at hw
    obtain rfl := Option.some.inj hw
    refine ⟨t, j, ?_⟩
    rw [hh t q (hqc t), Algo.step_eq_stepPair, Algo.stepPair_snd']
    exact List.mem_append_left _ hj

/-- M-notarisation を受けた genesis でないブロックには、9〜11 行で投票した正直者がいる。
    その段の入力 st2 の S に valid proposal がある。 -/
theorem exists_valid_proposal_vote (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) {b₂ : Block n Tx} (hg : b₂ ≠ .gen) (hM : ReceivesM f instrs b₂) :
    ∃ q t, Correct s₀ instrs q
      ∧ (Algo.st2 f lead q ((State.run s₀ instrs t).procs q)).view = b₂.view
      ∧ ValidProposal f lead (Algo.st2 f lead q ((State.run s₀ instrs t).procs q)).S
          (Algo.st2 f lead q ((State.run s₀ instrs t).procs q)).view b₂
      ∧ ∀ t' w j', Correct s₀ instrs w → Action.send (Msg.vote w b₂) j' ∈ (instrs t').actions w →
          t ≤ t' := by
  classical
  have hex :
      ∃ t, ∃ q, Correct s₀ instrs q ∧ ∃ j, Action.send (Msg.vote q b₂) j
      ∈ (instrs t).actions q := by
    rcases hM with rfl | hM
    · exact absurd rfl hg
    · obtain ⟨q, hq, hqc⟩ := exists_correct_of_lt_card hb (lt_of_lt_of_le (by omega) hM)
      obtain ⟨t, j, h⟩ := mem_voteSenders.mp hq
      exact ⟨t, q, hqc, j, h⟩
  obtain ⟨q, hqc, j, hj⟩ := Nat.find_spec hex
  have hmin : ∀ t' < Nat.find hex, ∀ w, Correct s₀ instrs w → ∀ j',
      Action.send (Msg.vote w b₂) j' ∈ (instrs t').actions w → False :=
    fun t' ht' w hw j' h => absurd (Nat.find_min' hex ⟨w, hw, j', h⟩) (not_le.mpr ht')
  -- Nat.find hex より前の S にある正直者の票はない
  have hnoS : ∀ w, Correct s₀ instrs w →
      Msg.vote w b₂ ∉ ((State.run s₀ instrs (Nat.find hex)).procs q).S := by
    intro w hw hmem
    obtain ⟨t', ht', j', hj'⟩ := sendsBefore_of_mem_S hinit hmem rfl (by simpa using hg)
    exact hmin t' ht' w hw j' hj'
  have hact := hh (Nat.find hex) q (hqc _)
  rw [hact] at hj
  -- 転送なら転送以外の段に遡る
  obtain ⟨j', hj'⟩ : ∃ j', Action.send (Msg.vote q b₂) j'
      ∈ Algo.innerActs f Δ lead q ((State.run s₀ instrs (Nat.find hex)).procs q) := by
    rw [Algo.step_eq_stepPair, Algo.stepPair_snd'] at hj
    rcases List.mem_append.mp hj with hj | hj
    · exact ⟨j, hj⟩
    · rcases Algo.mem_S_stage_or_sent f Δ lead q _ (Algo.send_forwardNew_mem hj)
        with hm | ⟨_, j', hs⟩
      · exact absurd hm (hnoS q hqc)
      · exact ⟨j', hs⟩
  simp only [Algo.innerActs, List.mem_append] at hj'
  rcases hj' with ((((hj' | hj') | hj') | hj') | hj')
  · -- 19〜21 行: S に M-notarisation があるので、それより前に正直者が投票している
    exfalso
    obtain ⟨b', q', hm, _, hqv, hM1, _, _, _, _, hnew, _⟩ :=
      Algo.send_climb (localInv_run hinit hh hqc _) hj'
    injection hm with _ hbb
    subst hbb
    obtain ⟨w, hw, hwc⟩ := exists_correct_of_lt_card hb
      (lt_of_lt_of_le (by omega) (show 2 * f + 1 ≤ _ from hM1))
    rcases hnew _ (mem_voters.mp hw) with hw' | ⟨b'', hb'', hlt⟩
    · exact hnoS w hwc hw'
    · injection hb'' with _ hbb
      subst hbb
      rw [hqv] at hlt
      exact absurd hlt (lt_irrefl _)
  · obtain ⟨_, hm, _⟩ := Algo.send_propose_eq hj'; cases hm
  · obtain ⟨b', hm, hbv, _, _, hvp, _⟩ := Algo.send_voteProposal_eq hj'
    injection hm with _ hbb
    subst hbb
    exact ⟨q, Nat.find hex, hqc, hbv.symm, hvp,
      fun t' w j' hw h => Nat.find_min' hex ⟨w, hw, j', h⟩⟩
  · obtain ⟨hm, _⟩ := Algo.send_nullifyTimeout_eq hj'; cases hm
  · obtain ⟨hm, _⟩ := Algo.send_nullifyNoProgress_eq hj'; cases hm

/-- 正直者の st2 の S にある M-notarisation は、実行上の M-notarisation。 -/
theorem receivesM_of_MNotarised_st2 (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {q : Fin n}
    (hqc : Correct s₀ instrs q) {t : Nat} {b₀ : Block n Tx}
    (h : MNotarised f (Algo.st2 f lead q ((State.run s₀ instrs t).procs q)).S b₀) :
    ReceivesM f instrs b₀ := by
  by_cases hg : b₀ = .gen
  · exact Or.inl hg
  · right
    refine h.trans (Finset.card_le_card fun w hw => ?_)
    rw [mem_voters] at hw
    rw [mem_voteSenders]
    exact sends_of_mem_S_st5 hinit hh hqc (Algo.S_st2_subset_st5 f Δ lead q _ hw) rfl
      (by simpa using hg)

theorem receivesNullification_of_Nullified_st2 (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    {q : Fin n} (hqc : Correct s₀ instrs q) {t : Nat} {w : View}
    (h : Nullified f (Algo.st2 f lead q ((State.run s₀ instrs t).procs q)).S w) :
    ReceivesNullification f instrs w := by
  refine h.trans (Finset.card_le_card fun x hx => ?_)
  rw [mem_nullifiers] at hx
  rw [mem_nullifySenders]
  exact sends_of_mem_S_st5 hinit hh hqc (Algo.S_st2_subset_st5 f Δ lead q _ hx) rfl (by simp)

/-- M-notarisation を受けたブロックの親は M-notarisation を受け、親の view と自分の view の
    間の view は nullification を受ける。 -/
theorem receivesM_parent (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) {q₀ : Fin n} {v : View} {tr : List Tx} {p₀ : Block n Tx}
    (hM : ReceivesM f instrs (Block.node q₀ v tr p₀)) :
    ReceivesM f instrs p₀
      ∧ ∀ w : View, p₀.view.val < w.val → w.val < v.val → ReceivesNullification f instrs w := by
  obtain ⟨q, t, hqc, hview, hvp, _⟩ := exists_valid_proposal_vote hinit hh hb (by simp) hM
  have hpar : p₀ ∈ (Block.node q₀ v tr p₀).parent := by simp [Block.parent]
  refine ⟨receivesM_of_MNotarised_st2 hinit hh hqc (hvp.parent p₀ hpar), fun w h1 h2 => ?_⟩
  refine receivesNullification_of_Nullified_st2 hinit hh hqc (hvp.gaps p₀ hpar w h1 ?_)
  rw [hview]; exact h2

/-- M-notarisation を受けたブロックの祖先は M-notarisation を受ける。 -/
theorem receivesM_ancestor (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) {c b : Block n Tx} (hanc : Block.Ancestor c b)
    (hM : ReceivesM f instrs b) : ReceivesM f instrs c := by
  induction hanc with
  | refl => exact hM
  | parent q v tr p _ ih => exact ih (receivesM_parent hinit hh hb hM).1

/-- Lemma 5.4（Consistency）の本体: L-notarisation を受けた 2 つのブロックは、一方が他方の
    祖先。 -/
theorem finalised_compatible (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {b b' : Block n Tx} (hL : ReceivesL f instrs b) (hL' : ReceivesL f instrs b') :
    b.Ancestor b' ∨ b'.Ancestor b := by
  by_contra hcon
  simp only [not_or] at hcon
  wlog hle : b.view.val ≤ b'.view.val generalizing b b' with H
  · exact H hL' hL ⟨hcon.2, hcon.1⟩ (not_le.mp hle).le
  have hbg : b ≠ .gen := fun h => hcon.1 (h ▸ Block.gen_ancestor b')
  have hv₁ := one_le_view_of_receivesL hn hinit hh hb hL hbg
  obtain ⟨q, v, tr, p₀, hanc, hge, hlt⟩ := Block.exists_crossing hv₁ hle
  have hM : ReceivesM f instrs (Block.node q v tr p₀) :=
    receivesM_ancestor hinit hh hb hanc (receivesM_of_receivesL hn hL')
  have hna : ¬ b.Ancestor (Block.node q v tr p₀) := fun h => hcon.1 (h.trans hanc)
  have hne : v.val ≠ b.view.val := by
    intro heq
    have hv : (Block.node q v tr p₀).view = b.view := View.val_injective heq
    have := receivesM_unique_of_receivesL hn hinit hh hb hL hv hM
    exact hna (this ▸ Block.Ancestor.refl _)
  obtain ⟨_, hgap⟩ := receivesM_parent hinit hh hb hM
  exact not_receivesNullification_of_receivesL hn hinit hh hb hL
    (hgap b.view hlt (lt_of_le_of_ne hge (Ne.symm hne)))

/-- S にある M-notarisation は、実行上の M-notarisation。 -/
theorem receivesM_of_MNotarised (hinit : Init s₀) {i : Fin n} {t : Nat} {b : Block n Tx}
    (h : MNotarised f ((State.run s₀ instrs t).procs i).S b) : ReceivesM f instrs b := by
  by_cases hg : b = .gen
  · exact Or.inl hg
  · right
    refine h.trans (Finset.card_le_card fun w hw => ?_)
    rw [mem_voters] at hw
    rw [mem_voteSenders]
    exact sends_of_mem_S hinit hw rfl (by simpa using hg)

/-- 正直者の S にある L-notarisation は、実行上の L-notarisation。 -/
theorem receivesL_of_LNotarised (hinit : Init s₀) {i : Fin n} {t : Nat} {b : Block n Tx}
    (h : LNotarised f ((State.run s₀ instrs t).procs i).S b) : ReceivesL f instrs b := by
  by_cases hg : b = .gen
  · exact Or.inl hg
  · right
    refine h.trans (Finset.card_le_card fun w hw => ?_)
    rw [mem_voters] at hw
    rw [mem_voteSenders]
    exact sends_of_mem_S hinit hw rfl (by simpa using hg)

/-- Consistency（§2）をブロックの形で: 2 つのプロセッサが L-notarisation を持つ 2 つの
    ブロックは、一方が他方の祖先。 -/
theorem consistency (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {i j : Fin n} {t t' : Nat} {b b' : Block n Tx}
    (hbi : LNotarised f ((State.run s₀ instrs t).procs i).S b)
    (hbj : LNotarised f ((State.run s₀ instrs t').procs j).S b') :
    b.Ancestor b' ∨ b'.Ancestor b :=
  finalised_compatible hn hinit hh hb (receivesL_of_LNotarised hinit hbi)
    (receivesL_of_LNotarised hinit hbj)

end Minimmit
