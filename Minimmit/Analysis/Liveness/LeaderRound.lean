import Minimmit.Analysis.Liveness.Lemma5_5

/-!
# Lemma 5.6 の補題群

最初の正直者が t ≥ GST に view v に入るとき: 全正直者は t + δ までに v に入る（`enter_all`）、
lead(v) は入ったスロット e に提案する、提案は t + 2δ までに全員の S で valid proposal になる、
正直者の view v の票はすべてこの提案への票で nullify(v) は誰も送らない、全正直者が投票する。
設定は `LeaderRound` にまとめ、`leader_round` で作る。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {GST : Time} {lead : View → Fin n} {s₀ : State n Tx}
  {instrs : Nat → Instr n Tx}

/-- 正直者 j の view が v を越えるなら、v から越えるスロットがある。 -/
theorem exists_leave_slot (hinit : Init s₀) {j : Fin n} {v : View} {t₁ : Nat} (hv : 1 ≤ v.val)
    (h : v.val < (viewAt s₀ instrs j t₁).val) :
    ∃ s < t₁, (viewAt s₀ instrs j s).val ≤ v.val ∧ v.val < (viewAt s₀ instrs j (s + 1)).val := by
  classical
  obtain ⟨t', rfl⟩ : ∃ t', t₁ = t' + 1 := by
    rcases t₁ with _ | t'
    · rw [viewAt_zero hinit] at h; omega
    · exact ⟨t', rfl⟩
  have hex : ∃ s, v.val < (viewAt s₀ instrs j (s + 1)).val := ⟨t', h⟩
  refine ⟨Nat.find hex, Nat.lt_succ_of_le (Nat.find_min' hex h), ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, viewAt_zero hinit]; exact hv
  · obtain ⟨s', hs'⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    rw [hs']
    exact not_lt.mp (Nat.find_min hex (by rw [hs']; exact Nat.lt_succ_self s'))

/-- 正直者がスロット s に view w の証明書を持てば、正直者は全員、期限までにそれを持つ。 -/
theorem hasCert_all (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ GST s₀ instrs)
    {j : Fin n} (hj : Correct s₀ instrs j) {s : Nat} {w : View} (hw : 1 ≤ w.val)
    (h : Algo.HasCert f ((State.run s₀ instrs s).procs j).S w) {q : Fin n}
    {T : Nat} (hT₁ : s + 1 ≤ T) (hT₂ : max GST.val s + δ ≤ T) :
    Algo.HasCert f ((State.run s₀ instrs T).procs q).S w := by
  rcases h with h | h
  · exact Or.inl (nullified_all hinit hh hs hj h hT₁ hT₂)
  · obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨hbv, hM⟩ := Algo.mem_mNotarisedAt hb
    have hg : b ≠ .gen := by
      intro hg
      subst hg
      have : w.val = 0 := by rw [← hbv]; rfl
      omega
    have := mnotarised_all (j := q) hinit hh hs hj hM hT₁ hT₂
    rw [← hbv]
    exact Algo.hasCert_of_mnotarised this

/-- Lemma 5.6 の第 1 段: 最初の正直者が t に view v に入れば、正直者は全員
    max(t, GST) + δ までに view v に入る。T₀ は t 以上で GST 以上の任意の時刻。 -/
theorem enter_all_anchor (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ GST s₀ instrs) {v : View} {t : Nat} (hfirst : FirstEntry s₀ instrs v t)
    {T₀ : Nat} (ht : t ≤ T₀) (hgst : GST.val ≤ T₀) {q : Fin n} (hq : Correct s₀ instrs q) :
    v.val ≤ (viewAt s₀ instrs q (T₀ + δ + 1)).val := by
  obtain ⟨j, hj, hjv⟩ := hfirst.entered
  have hδ1 := hs.one_le
  rw [viewAt_succ_eq hh hq (T₀ + δ)]
  apply Algo.st1_reaches q
  intro w h1 h2
  have hw1 : 1 ≤ w.val := le_trans (viewAt_pos hinit hh hq (T₀ + δ)) h1
  obtain ⟨s, hs_lt, hs1, hs2⟩ := exists_leave_slot hinit hw1 (lt_of_lt_of_le h2 hjv)
  have hcert : Algo.HasCert f ((State.run s₀ instrs s).procs j).S w := by
    rw [viewAt_succ_eq hh hj s] at hs2
    exact Algo.st1_certs hs1 hs2
  exact hasCert_all hinit hh hs hj hw1 hcert (by omega) (by omega)

/-- 最初の正直者が t ≥ GST に view v に入れば、正直者は全員 t + δ までに view v に入る。 -/
theorem enter_all (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ GST s₀ instrs)
    {v : View} {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : GST.val ≤ t) {q : Fin n}
    (hq : Correct s₀ instrs q) : v.val ≤ (viewAt s₀ instrs q (t + δ + 1)).val :=
  enter_all_anchor hinit hh hs hfirst (le_refl t) hgst hq

/-- 初めて受け取った取引は、そのスロットの終わりに全員へ転送される。 -/
theorem tx_forwarded (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {tr : Tx}
    (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S)
    (hfirst : ∀ t' < t, Msg.tx tr ∉ ((State.run s₀ instrs t').procs i).S) (j : Fin n) :
    Action.send (Msg.tx tr) j ∈ (instrs t).actions i := by
  have hnew : Msg.tx tr ∉ (Algo.st5 f Δ lead i ((State.run s₀ instrs t).procs i)).prevS := by
    rw [Algo.st5_prevS]
    cases t with
    | zero => rw [prevS_zero hinit]; simp [mem_genesisS]
    | succ t' =>
      rw [prevS_run_honest hh hi]
      intro hm
      rcases Algo.mem_S_stage_or f Δ lead i _ hm with hm | hsig
      · exact hfirst t' (Nat.lt_succ_self t') hm
      · exact absurd hsig (by simp [Msg.signer])
  have hmem : Msg.tx tr ∈ (Algo.st5 f Δ lead i ((State.run s₀ instrs t).procs i)).S :=
    Algo.S_subset_st5 f Δ lead i _ htr
  rw [hh t i (hi t)]
  exact Algo.send_mem_step_of_mem_forwardMsgs (Algo.mem_forwardMsgs_tx hmem hnew) j


/-- 有限個の ∃ s は、共通の上界 T 以下の s で取れる。 -/
theorem exists_bound {α : Type} {Q : Finset α} {P : α → Nat → Prop} (h : ∀ q ∈ Q, ∃ s, P q s) :
    ∃ T, ∀ q ∈ Q, ∃ s ≤ T, P q s := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨0, fun q hq => by simp at hq⟩
  | @insert a Q ha ih =>
    obtain ⟨T, hT⟩ := ih fun q hq => h q (Finset.mem_insert_of_mem hq)
    obtain ⟨s, hs⟩ := h a (Finset.mem_insert_self a Q)
    refine ⟨max T s, fun q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨s, le_max_right _ _, hs⟩
    · obtain ⟨s', hs', hP⟩ := hT q hq
      exact ⟨s', hs'.trans (le_max_left _ _), hP⟩

/-- lead(v) の提案の Tr* には、その時点で受信済みの取引がすべて入る。 -/
theorem mem_trStar_leaderBlock {f : Nat} {i : Fin n} {p : Processor n Tx} {tr : Tx}
    (h : Msg.tx tr ∈ p.S) : tr ∈ (Algo.leaderBlock f i p).trStar := by
  rw [Algo.leaderBlock, Block.mem_trStar_node]
  by_cases hp : tr ∈ (Algo.selectParent f p.S p.view).trStar
  · exact Or.inl hp
  · right
    simp only [Algo.payload, List.mem_filter, List.mem_filterMap, Finset.mem_toList,
      decide_eq_true_eq]
    exact ⟨⟨Msg.tx tr, h, rfl⟩, hp⟩

/-! ### 5.6 の補題 -/

/-- 正直者 r が view v 以上に達するなら、初めて達するスロット e がある。 -/
theorem entry_slot (hinit : Init s₀) {r : Fin n} {v : View} (hv : 1 ≤ v.val)
    (hreach : ∃ s, v.val ≤ (viewAt s₀ instrs r (s + 1)).val) :
    ∃ e, v.val ≤ (viewAt s₀ instrs r (e + 1)).val
      ∧ (∀ s' < e, (viewAt s₀ instrs r (s' + 1)).val < v.val)
      ∧ ((viewAt s₀ instrs r e).val < v.val ∨ (e = 0 ∧ v.val = 1)) := by
  classical
  refine ⟨Nat.find hreach, Nat.find_spec hreach,
    fun s' hs' => not_le.mp (Nat.find_min hreach hs'), ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hreach) with h0 | hpos
  · rw [h0, viewAt_zero hinit]
    rcases Nat.lt_or_ge 1 v.val with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, le_antisymm h hv⟩
  · obtain ⟨s', hs'⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    left; rw [hs']
    exact not_le.mp (Nat.find_min hreach (by rw [hs']; exact Nat.lt_succ_self s'))

/-- lead(v) が view v に入るスロット e より前に、正直者は view v のブロックに投票しない。
    e より前に投票するには lead(v) の署名付きの view v のブロックか、それへの正直者の票が
    要るから。 -/
theorem vote_slot_ge (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {v : View} (hv : 1 ≤ v.val) (hlc : Correct s₀ instrs (lead v)) {e : Nat}
    (hemin : ∀ s' < e, (viewAt s₀ instrs (lead v) (s' + 1)).val < v.val) :
    ∀ s, ∀ r : Fin n, Correct s₀ instrs r → ∀ b : Block n Tx, b.view = v → ∀ j,
      Action.send (Msg.vote r b) j ∈ (instrs s).actions r → e ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro r hr b hbv j hj
  rcases Nat.lt_or_ge s e with hlt | hge
  swap
  · exact hge
  exfalso
  have hg : b ≠ .gen := by
    intro hg; subst hg
    have : v.val = 0 := by rw [← hbv]; rfl
    omega
  have hact := hh s r (hr s)
  rw [hact] at hj
  obtain ⟨j', hj'⟩ : ∃ j', Action.send (Msg.vote r b) j'
      ∈ Algo.innerActs f Δ lead r ((State.run s₀ instrs s).procs r) := by
    rw [Algo.step_eq_stepPair, Algo.stepPair_snd'] at hj
    rcases List.mem_append.mp hj with hj | hj
    · exact ⟨j, hj⟩
    · rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.send_forwardNew_mem hj)
        with hm | ⟨_, j', hs'⟩
      · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hm rfl (by simpa using hg)
        exact absurd (ih s' hs' r hr b hbv j'' hj'') (not_le.mpr (lt_trans hs' hlt))
      · exact ⟨j', hs'⟩
  have hsend : Action.send (Msg.vote r b) j' ∈ (instrs s).actions r := by
    rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd']
    exact List.mem_append_left _ hj'
  simp only [Algo.innerActs, List.mem_append] at hj'
  rcases hj' with ((((hj' | hj') | hj') | hj') | hj')
  · -- 登り: 中間状態 q の S に b の M-notarisation。正直な投票者がそれより前に投票している
    obtain ⟨b', q, hm, _, hqv, hM, _, _, _, _, hnew, _⟩ :=
      Algo.send_climb (localInv_run hinit hh hr s) hj'
    injection hm with _ hbb
    subst hbb
    obtain ⟨w, hw, hwc⟩ := exists_correct_of_lt_card hb
      (lt_of_lt_of_le (by omega) (show 2 * f + 1 ≤ _ from hM))
    rcases hnew _ (mem_voters.mp hw) with hw' | ⟨b'', hb'', hlt'⟩
    · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hw' rfl (by simpa using hg)
      exact absurd (ih s' hs' w hwc b hbv j'' hj'') (not_le.mpr (lt_trans hs' hlt))
    · injection hb'' with _ hbb
      subst hbb
      rw [hqv] at hlt'
      exact absurd hlt' (lt_irrefl _)
  · obtain ⟨_, hm, _⟩ := Algo.send_propose_eq hj'; cases hm
  · -- 9〜11 行: 票の対象は lead(v) の署名付きブロック。lead(v) は s の終わりに view v 以上
    obtain ⟨b', hm, hbv', _, _, hvp, _⟩ := Algo.send_voteProposal_eq hj'
    injection hm with _ hbb
    subst hbb
    have hsigned := hvp.signed
    have hlv : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view = v := by
      rw [← hbv, hbv']
    rw [hlv] at hsigned
    have hle := own_block_view_le hinit hh hlc hsigned (containsBlock_succ_of_send hh hr hsend rfl)
    have h1 := hemin s hlt
    rw [hbv] at hle
    exact absurd (lt_of_le_of_lt hle h1) (lt_irrefl _)
  · obtain ⟨hm, _⟩ := Algo.send_nullifyTimeout_eq hj'; cases hm
  · obtain ⟨hm, _⟩ := Algo.send_nullifyNoProgress_eq hj'; cases hm

/-- lead(v) が view v に入るスロット e より前に、正直者は nullify(v) を送らない。 -/
theorem nullify_slot_ge (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) (hs : PartialSync δ GST s₀ instrs) (hδ : δ ≤ Δ) {v : View}
    (hv : 1 ≤ v.val)
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hlc : Correct s₀ instrs (lead v)) {e : Nat}
    (he : e ≤ t + δ) (hemin : ∀ s' < e, (viewAt s₀ instrs (lead v) (s' + 1)).val < v.val) :
    ∀ s, ∀ r : Fin n, Correct s₀ instrs r → ∀ j,
      Action.send (Msg.nullify r v) j ∈ (instrs s).actions r → e ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro r hr j hj
  rcases Nat.lt_or_ge s e with hlt | hge
  swap
  · exact hge
  exfalso
  have hδ1 := hs.one_le
  have hact := hh s r (hr s)
  rw [hact] at hj
  obtain ⟨j', hj'⟩ : ∃ j', Action.send (Msg.nullify r v) j'
      ∈ Algo.innerActs f Δ lead r ((State.run s₀ instrs s).procs r) := by
    rw [Algo.step_eq_stepPair, Algo.stepPair_snd'] at hj
    rcases List.mem_append.mp hj with hj | hj
    · exact ⟨j, hj⟩
    · rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.send_forwardNew_mem hj)
        with hm | ⟨_, j', hs'⟩
      · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hm rfl nofun
        exact absurd (ih s' hs' r hr j'' hj'') (not_le.mpr (lt_trans hs' hlt))
      · exact ⟨j', hs'⟩
  simp only [Algo.innerActs, List.mem_append] at hj'
  rcases hj' with ((((hj' | hj') | hj') | hj') | hj')
  · obtain ⟨_, _, hm, _⟩ := Algo.send_climb (localInv_run hinit hh hr s) hj'; cases hm
  · obtain ⟨_, hm, _⟩ := Algo.send_propose_eq hj'; cases hm
  · obtain ⟨_, hm, _⟩ := Algo.send_voteProposal_eq hj'; cases hm
  · -- 13〜14 行: r は 2Δ スロット前から view v にいるので、t ≤ s − 2Δ
    obtain ⟨hm, _, _, _, ht3⟩ := Algo.send_nullifyTimeout_eq hj'
    injection hm with _ hv3
    rw [Algo.st3_timer] at ht3
    have hst1 :
        Algo.st1 f r ((State.run s₀ instrs s).procs r) = (State.run s₀ instrs s).procs r := by
      rcases Algo.st1_eq_or f r ((State.run s₀ instrs s).procs r) with h | ⟨h, _⟩
      · exact h
      · rw [h] at ht3; omega
    have htimer : timerAt s₀ instrs r s = 2 * Δ := by
      show ((State.run s₀ instrs s).procs r).timer = 2 * Δ
      rw [← hst1]; exact ht3
    have hview : viewAt s₀ instrs r s = v := by
      show ((State.run s₀ instrs s).procs r).view = v
      rw [hv3, Algo.st3_view, hst1]
    have hle := timerAt_le_slot (instrs := instrs) hinit r s
    rw [htimer] at hle
    have hstay := viewAt_eq_of_lt_timer hinit r s (2 * Δ - 1) (by rw [htimer]; omega) (2 * Δ - 1)
      (le_refl _)
    rw [show s - (2 * Δ - 1) = (s - 2 * Δ) + 1 by omega, hview] at hstay
    have := hfirst.first r (s - 2 * Δ) hr (by rw [hstay])
    omega
  · -- 24〜28 行: r は view v のブロック c₀ に投票済みで、その票は e 以降
    obtain ⟨hm, _, c₀, hc₀, _⟩ := Algo.send_nullifyNoProgress_eq hj'
    injection hm with _ hv4
    have hL4 := Algo.localInv_st4 (Δ := Δ) (lead := lead) (localInv_run hinit hh hr s)
    have hvote := hL4.notar_mem c₀ hc₀
    have hcv : c₀.view = v := (hL4.notar_view c₀ hc₀).trans hv4.symm
    rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.S_st4_subset_st5 f Δ lead r _ hvote)
      with hm' | ⟨_, j'', hs''⟩
    · obtain ⟨s', hs', j₃, hj₃⟩ := sendsBefore_of_mem_S hinit hm' rfl
        (Msg.vote_ne_gen_vote (by rw [hcv]; omega))
      exact absurd (vote_slot_ge hinit hh hb hv hlc hemin s' r hr c₀ hcv j₃ hj₃)
        (not_le.mpr (lt_trans hs' hlt))
    · have hsend : Action.send (Msg.vote r c₀) j'' ∈ (instrs s).actions r := by
        rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd']
        exact List.mem_append_left _ hs''
      exact absurd (vote_slot_ge hinit hh hb hv hlc hemin s r hr c₀ hcv j'' hsend) (not_le.mpr hlt)

/-- lead(v) が view v に入るスロット e の冒頭の S に、view v の証明書はない。 -/
theorem no_cert_at_entry (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) (hs : PartialSync δ GST s₀ instrs) (hδ : δ ≤ Δ) {v : View}
    (hv : 1 ≤ v.val)
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hlc : Correct s₀ instrs (lead v)) {e : Nat}
    (he : e ≤ t + δ) (hemin : ∀ s' < e, (viewAt s₀ instrs (lead v) (s' + 1)).val < v.val) :
    ¬ Algo.HasCert f ((State.run s₀ instrs e).procs (lead v)).S v := by
  intro hc
  rcases hc with hN | hM
  · have hcard := card_le_of_byz hb (nullifiers ((State.run s₀ instrs e).procs (lead v)).S v)
      fun q hq => exists_byz_of_not_correct fun hqc => ?_
    · unfold Nullified at hN; omega
    · obtain ⟨s', hs', j, hj⟩ := sendsBefore_of_mem_S hinit (mem_nullifiers.mp hq) rfl (by simp)
      exact absurd (nullify_slot_ge hinit hh hb hs hδ hv hfirst hlc he hemin s' q hqc j hj)
        (not_le.mpr hs')
  · obtain ⟨b', hb'⟩ := List.exists_mem_of_ne_nil _ hM
    obtain ⟨hbv, hM'⟩ := Algo.mem_mNotarisedAt hb'
    have hg : b' ≠ .gen := by
      intro hg; subst hg
      have : v.val = 0 := by rw [← hbv]; rfl
      omega
    have hcard := card_le_of_byz hb (voters ((State.run s₀ instrs e).procs (lead v)).S b')
      fun q hq => exists_byz_of_not_correct fun hqc => ?_
    · unfold MNotarised at hM'; omega
    · obtain ⟨s', hs', j, hj⟩ := sendsBefore_of_mem_S hinit (mem_voters.mp hq) rfl
        (by simpa using hg)
      exact absurd (vote_slot_ge hinit hh hb hv hlc hemin s' q hqc b' hbv j hj) (not_le.mpr hs')

/-- lead(v) は view v に入るスロット e に、登りを view v で終え、まだ提案していない。 -/
theorem leader_at_entry (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) (hs : PartialSync δ GST s₀ instrs) (hδ : δ ≤ Δ) {v : View}
    (hv : 1 ≤ v.val)
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hlc : Correct s₀ instrs (lead v)) {e : Nat}
    (he : e ≤ t + δ) (hev : v.val ≤ (viewAt s₀ instrs (lead v) (e + 1)).val)
    (hemin : ∀ s' < e, (viewAt s₀ instrs (lead v) (s' + 1)).val < v.val)
    (hstart : (viewAt s₀ instrs (lead v) e).val < v.val ∨ (e = 0 ∧ v.val = 1)) :
    (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).view = v
      ∧ (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).proposed = false := by
  have hnc := no_cert_at_entry hinit hh hb hs hδ hv hfirst hlc he hemin
  rw [viewAt_succ_eq hh hlc e] at hev
  have hle : (viewAt s₀ instrs (lead v) e).val ≤ v.val := by
    rcases hstart with h | ⟨rfl, h⟩
    · exact h.le
    · rw [viewAt_zero hinit]; omega
  have hview : (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).view = v := by
    apply View.val_injective
    rcases Nat.lt_or_ge v.val
        (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).view.val
      with hlt | hge
    · exact absurd (Algo.st1_certs hle hlt) hnc
    · exact le_antisymm hge hev
  refine ⟨hview, ?_⟩
  rcases Algo.st1_eq_or f (lead v) ((State.run s₀ instrs e).procs (lead v)) with h | ⟨_, h⟩
  · rw [h]
    rcases hstart with hlt | ⟨rfl, _⟩
    · exfalso
      rw [h] at hview
      have : (viewAt s₀ instrs (lead v) e).val = v.val := congrArg View.val hview
      omega
    · show ((State.run s₀ instrs 0).procs (lead v)).proposed = false
      rw [State.run, hinit.procs]; rfl
  · exact h

/-- Lemma 5.6 の設定: view v ≥ 1 の lead(v) は正直で、最初の正直者が t ≥ GST に view v に入り、
    lead(v) 自身は t ≤ e ≤ t + δ のスロット e に初めて view v 以上になる。δ ≤ Δ は GST 後の
    実際の遅延の上界。 -/
structure LeaderRound (f Δ δ : Nat) (lead : View → Fin n) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) (GST : Time) (v : View) (t e : Nat) : Prop where
  hn : 5 * f + 1 ≤ n
  hδ : δ ≤ Δ
  hv : 1 ≤ v.val
  hfirst : FirstEntry s₀ instrs v t
  hgst : GST.val ≤ t
  hlc : Correct s₀ instrs (lead v)
  he : e ≤ t + δ
  hev : v.val ≤ (viewAt s₀ instrs (lead v) (e + 1)).val
  hemin : ∀ s' < e, (viewAt s₀ instrs (lead v) (s' + 1)).val < v.val
  hstart : (viewAt s₀ instrs (lead v) e).val < v.val ∨ (e = 0 ∧ v.val = 1)

/-- lead(v) がスロット e に提案するブロック -/
noncomputable def leaderBlockAt (f : Nat) (lead : View → Fin n) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) (v : View) (e : Nat) : Block n Tx :=
  Algo.leaderBlock f (lead v) (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v)))

/-- その親 -/
noncomputable def leaderParentAt (f : Nat) (lead : View → Fin n) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) (v : View) (e : Nat) : Block n Tx :=
  Algo.selectParent f (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).S
    (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).view

theorem leaderBlockAt_parent (f : Nat) (lead : View → Fin n) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) (v : View) (e : Nat) :
    (leaderBlockAt f lead s₀ instrs v e).parent = some (leaderParentAt f lead s₀ instrs v e) := rfl

section CorrectLeader

variable (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
  (hs : PartialSync δ GST s₀ instrs) {v : View} {t e : Nat}
  (R : LeaderRound f Δ δ lead s₀ instrs GST v t e)

include hinit hh hb hs R

theorem leaderBlockAt_view : (leaderBlockAt f lead s₀ instrs v e).view = v :=
  (leader_at_entry hinit hh hb hs R.hδ R.hv R.hfirst R.hlc R.he R.hev R.hemin R.hstart).1

theorem leaderParentAt_view_lt : (leaderParentAt f lead s₀ instrs v e).view.val < v.val := by
  have hview :=
      (leader_at_entry hinit hh hb hs R.hδ R.hv R.hfirst R.hlc R.he R.hev R.hemin R.hstart).1
  unfold leaderParentAt
  rw [hview]
  exact Algo.selectParent_view_lt f _ R.hv

/-- lead(v) はスロット e にブロックを全員へ送る。 -/
theorem leader_proposes (j : Fin n) :
    Action.send (Msg.propose (leaderBlockAt f lead s₀ instrs v e)) j
      ∈ (instrs e).actions (lead v) := by
  obtain ⟨hview, hprop⟩ :=
    leader_at_entry hinit hh hb hs R.hδ R.hv R.hfirst R.hlc R.he R.hev R.hemin R.hstart
  rw [hh e (lead v) (R.hlc e), Algo.step_eq_stepPair, Algo.stepPair_snd']
  apply List.mem_append_left
  simp only [Algo.innerActs, List.mem_append]
  left; left; left; right
  exact Algo.propose_fires (by rw [hview]) hprop j

omit hinit hh hb hs in
theorem first_entry_le_leader_entry : t ≤ e := R.hfirst.first (lead v) e R.hlc R.hev

/-- ブロックは t + 2δ までに全正直者に届く。 -/
theorem leader_block_delivered {r : Fin n} {T : Nat} (hT : t + 2 * δ ≤ T) :
    Msg.propose (leaderBlockAt f lead s₀ instrs v e) ∈ ((State.run s₀ instrs T).procs r).S := by
  have hδ1 := hs.one_le
  have hδ := R.hδ
  have he := R.he
  have hgst := R.hgst
  exact delivered hinit hh hs R.hlc (leader_proposes hinit hh hb hs R r) (by omega) (by omega)

omit hb in
/-- 親の M-notarisation は t + 2δ までに全正直者に届く。 -/
theorem leader_parent_mnotarised_all {r : Fin n} {T : Nat} (hT : t + 2 * δ ≤ T) :
    MNotarised f ((State.run s₀ instrs T).procs r).S (leaderParentAt f lead s₀ instrs v e) := by
  have hδ1 := hs.one_le
  have hδ := R.hδ
  have he := R.he
  have hgst := R.hgst
  have h1 : MNotarised f (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).S
      (leaderParentAt f lead s₀ instrs v e) :=
    Algo.selectParent_mnotarised (by have := R.hn; omega)
      ((genesisS_subset_run hinit (lead v) e).trans (Algo.S_subset_st1 f (lead v) _)) _
  have h5 := h1.mono (Algo.S_st1_subset_st5 f Δ lead (lead v) _)
  exact mnotarised_all_end hinit hh hs R.hlc h5 (by omega) (by omega)

/-- 親の view と v の間の view の nullification は t + 2δ までに全正直者に届く。 -/
theorem leader_gaps_nullified_all {r : Fin n} {T : Nat}
    (hT : t + 2 * δ ≤ T) {w : View}
    (h1 : (leaderParentAt f lead s₀ instrs v e).view.val < w.val) (h2 : w.val < v.val) :
    Nullified f ((State.run s₀ instrs T).procs r).S w := by
  have hδ1 := hs.one_le
  have hδ := R.hδ
  have he := R.he
  have hgst := R.hgst
  have hview :=
      (leader_at_entry hinit hh hb hs R.hδ R.hv R.hfirst R.hlc R.he R.hev R.hemin R.hstart).1
  have hw1 : 1 ≤ w.val := by omega
  obtain ⟨s', hs'_lt, hs1, hs2⟩ := exists_leave_slot hinit hw1 (lt_of_lt_of_le h2 R.hev)
  have hcert : Algo.HasCert f ((State.run s₀ instrs s').procs (lead v)).S w := by
    rw [viewAt_succ_eq hh R.hlc s'] at hs2
    exact Algo.st1_certs hs1 hs2
  rcases hcert with hN | hM
  · exact nullified_all hinit hh hs R.hlc hN (by omega) (by omega)
  · exfalso
    obtain ⟨b'', hb''⟩ := List.exists_mem_of_ne_nil _ hM
    obtain ⟨hbv, hM''⟩ := Algo.mem_mNotarisedAt hb''
    have hsub : ((State.run s₀ instrs s').procs (lead v)).S
        ⊆ (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).S :=
      (S_subset_run s₀ instrs (lead v) (Nat.lt_succ_iff.mp hs'_lt)).trans
        (Algo.S_subset_st1 f (lead v) _)
    obtain ⟨q, hq⟩ := Algo.exists_vote_of_mem_votedBlocks
        (Algo.mem_votedBlocks_of_mem_mNotarisedAt hb'')
    have hmax := Algo.selectParent_max f
      (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).S
      (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).view
      (Algo.mem_votedBlocks (hsub hq)) (by rw [hbv, hview]; exact h2) (hM''.mono hsub)
    rw [hbv] at hmax
    exact absurd h1 (not_lt.mpr hmax)

/-- t + 2δ 以降、全正直者の S でブロックは valid proposal。 -/
theorem leader_valid_at {r : Fin n} {T : Nat} (hT : t + 2 * δ ≤ T) :
    ValidProposal f lead ((State.run s₀ instrs T).procs r).S v
    (leaderBlockAt f lead s₀ instrs v e) := by
  refine ⟨leaderBlockAt_view hinit hh hb hs R, rfl,
    ⟨_, leader_block_delivered hinit hh hb hs R hT, rfl⟩, ?_, Algo.leaderBlock_ne_gen _ _ _, ?_, ?_⟩
  · intro b' hb'v hb's hb'
    exact own_block_eq_of_send hinit hh R.hlc hb' hb's (leader_proposes hinit hh hb hs R r)
      (by rw [hb'v, leaderBlockAt_view hinit hh hb hs R])
  · intro p₀ hp₀
    rw [leaderBlockAt_parent] at hp₀
    obtain rfl := Option.some.inj (Option.mem_def.mp hp₀).symm
    exact leader_parent_mnotarised_all hinit hh hs R hT
  · intro p₀ hp₀ w h1 h2
    rw [leaderBlockAt_parent] at hp₀
    obtain rfl := Option.some.inj (Option.mem_def.mp hp₀).symm
    exact leader_gaps_nullified_all hinit hh hb hs R hT h1 h2

/-- 正直者の view v のブロックへの票は、すべて lead(v) のブロックへの票。 -/
theorem vote_unique_leaderBlock :
    ∀ s, ∀ r : Fin n, Correct s₀ instrs r → ∀ b : Block n Tx, b.view = v → ∀ j,
      Action.send (Msg.vote r b) j ∈ (instrs s).actions r →
      b = leaderBlockAt f lead s₀ instrs v e := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro r hr b hbv j hj
  have hv := R.hv
  have hg : b ≠ .gen := by
    intro hg; subst hg
    have : v.val = 0 := by rw [← hbv]; rfl
    omega
  have hact := hh s r (hr s)
  have hinner : ∀ j', Action.send (Msg.vote r b) j'
      ∈ Algo.innerActs f Δ lead r ((State.run s₀ instrs s).procs r) →
      b = leaderBlockAt f lead s₀ instrs v e := by
    intro j' hj'
    have hsend : Action.send (Msg.vote r b) j' ∈ (instrs s).actions r := by
      rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd']
      exact List.mem_append_left _ hj'
    simp only [Algo.innerActs, List.mem_append] at hj'
    rcases hj' with ((((hj' | hj') | hj') | hj') | hj')
    · obtain ⟨b', q, hm, _, hqv, hM, _, _, _, _, hnew, _⟩ :=
        Algo.send_climb (localInv_run hinit hh hr s) hj'
      injection hm with _ hbb
      subst hbb
      obtain ⟨w, hw, hwc⟩ := exists_correct_of_lt_card hb
        (lt_of_lt_of_le (by omega) (show 2 * f + 1 ≤ _ from hM))
      rcases hnew _ (mem_voters.mp hw) with hw' | ⟨b'', hb'', hlt'⟩
      · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hw' rfl (by simpa using hg)
        exact ih s' hs' w hwc b hbv j'' hj''
      · injection hb'' with _ hbb
        subst hbb
        rw [hqv] at hlt'
        exact absurd hlt' (lt_irrefl _)
    · obtain ⟨_, hm, _⟩ := Algo.send_propose_eq hj'; cases hm
    · obtain ⟨b', hm, hbv', _, _, hvp, _⟩ := Algo.send_voteProposal_eq hj'
      injection hm with _ hbb
      subst hbb
      have hsigned := hvp.signed
      have hlv : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view = v := by
        rw [← hbv, hbv']
      rw [hlv] at hsigned
      exact own_block_eq_of_send hinit hh R.hlc (containsBlock_succ_of_send hh hr hsend rfl)
        hsigned (leader_proposes hinit hh hb hs R r)
        (by rw [hbv, leaderBlockAt_view hinit hh hb hs R])
    · obtain ⟨hm, _⟩ := Algo.send_nullifyTimeout_eq hj'; cases hm
    · obtain ⟨hm, _⟩ := Algo.send_nullifyNoProgress_eq hj'; cases hm
  rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd'] at hj
  rcases List.mem_append.mp hj with hj | hj
  · exact hinner j hj
  · rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.send_forwardNew_mem hj)
      with hm | ⟨_, j', hs'⟩
    · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hm rfl (by simpa using hg)
      exact ih s' hs' r hr b hbv j'' hj''
    · exact hinner j' hs'

/-- 正直者は timeout で nullify(v) を送らない: timeout の時点で lead(v) のブロックは valid
    proposal として届いていて、9〜11 行が先に投票するから。 -/
theorem no_timeout_nullify :
    ∀ s, ∀ r : Fin n, Correct s₀ instrs r → ∀ j,
      Action.send (Msg.nullify r v) j
        ∈ (Algo.nullifyTimeout Δ r (Algo.st3 f lead r ((State.run s₀ instrs s).procs r))).2 →
      False := by
  intro s r hr j hj
  have hδ1 := hs.one_le
  have hδ := R.hδ
  have hv := R.hv
  obtain ⟨hm, hnl3, hnot3, _, ht3⟩ := Algo.send_nullifyTimeout_eq hj
  injection hm with _ hv3
  rw [Algo.st3_timer] at ht3
  have hst1 : Algo.st1 f r ((State.run s₀ instrs s).procs r) = (State.run s₀ instrs s).procs r := by
    rcases Algo.st1_eq_or f r ((State.run s₀ instrs s).procs r) with h | ⟨h, _⟩
    · exact h
    · rw [h] at ht3; omega
  have htimer : timerAt s₀ instrs r s = 2 * Δ := by
    show ((State.run s₀ instrs s).procs r).timer = 2 * Δ
    rw [← hst1]; exact ht3
  have hview : viewAt s₀ instrs r s = v := by
    show ((State.run s₀ instrs s).procs r).view = v
    rw [hv3, Algo.st3_view, hst1]
  -- t + 2Δ ≤ s
  have hle := timerAt_le_slot (instrs := instrs) hinit r s
  rw [htimer] at hle
  have hstay := viewAt_eq_of_lt_timer hinit r s (2 * Δ - 1) (by rw [htimer]; omega) (2 * Δ - 1)
    (le_refl _)
  rw [show s - (2 * Δ - 1) = (s - 2 * Δ) + 1 by omega, hview] at hstay
  have hT : t + 2 * Δ ≤ s := by
    have := R.hfirst.first r (s - 2 * Δ) hr (by rw [hstay])
    omega
  -- lead(v) のブロックは S にあり valid
  have hvalid := leader_valid_at (r := r) hinit hh hb hs R (T := s) (by omega)
  have hst2S : ((State.run s₀ instrs s).procs r).S
      ⊆ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S :=
    Algo.S_subset_st2 f lead r _
  have hst2v : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view = v := by
    rw [Algo.st2_view, hst1]; exact hview
  have hbLv := leaderBlockAt_view hinit hh hb hs R
  have huniq : ∀ b', b'.view = (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view →
      b'.signer = some (lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view) →
      containsBlock (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S b' →
      b' = leaderBlockAt f lead s₀ instrs v e := by
    intro b' hb'v hb's hb'
    rw [hst2v] at hb'v hb's
    have hc := containsBlock_mono
      ((Algo.S_st2_subset_st5 f Δ lead r _).trans (S_st5_subset_succ hh hr s)) hb'
    exact own_block_eq_of_send hinit hh R.hlc hc hb's (leader_proposes hinit hh hb hs R r)
      (by rw [hb'v, hbLv])
  have hvp2 : ValidProposal f lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S
      (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view
      (leaderBlockAt f lead s₀ instrs v e) :=
    ⟨by rw [hst2v]; exact hbLv, by rw [hst2v]; rfl, containsBlock_mono hst2S hvalid.mem, huniq,
      Algo.leaderBlock_ne_gen _ _ _, fun p₀ hp₀ => (hvalid.parent p₀ hp₀).mono hst2S,
      fun p₀ hp₀ w h1 h2 => (hvalid.gaps p₀ hp₀ w h1 (by rw [hst2v] at h2; exact h2)).mono hst2S⟩
  have hprop : Algo.proposals lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S
      (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view
      = [leaderBlockAt f lead s₀ instrs v e] :=
    Algo.proposals_eq_singleton (containsBlock_mono hst2S hvalid.mem) (by rw [hst2v]; rfl)
      (by rw [hst2v]; exact hbLv) huniq
  have h3 := Algo.voteProposal_eq_of_singleton (f := f) (i := r) hprop
  have hnot3' :
      (Algo.voteProposal f lead r (Algo.st2 f lead r ((State.run s₀ instrs s).procs r))).1.notarised
      = none := hnot3
  have hnl3' :
      (Algo.voteProposal f lead r (Algo.st2 f lead r ((State.run s₀ instrs s).procs r))).1.nullified
      = false := hnl3
  rw [h3] at hnot3' hnl3'
  split_ifs at hnot3' hnl3' with hcond
  · rw [Algo.disseminate_vote_notarised (by rw [hst2v]; exact hbLv)] at hnot3'
    cases hnot3'
  · exact hcond ⟨hvp2, hnot3', hnl3'⟩

/-- 正直者は nullify(v) を送らない。 -/
theorem no_nullify_v :
    ∀ s, ∀ r : Fin n, Correct s₀ instrs r → ∀ j,
      Action.send (Msg.nullify r v) j ∈ (instrs s).actions r → False := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro r hr j hj
  have hact := hh s r (hr s)
  have hinner : ∀ j', Action.send (Msg.nullify r v) j'
      ∈ Algo.innerActs f Δ lead r ((State.run s₀ instrs s).procs r) → False := by
    intro j' hj'
    simp only [Algo.innerActs, List.mem_append] at hj'
    rcases hj' with ((((hj' | hj') | hj') | hj') | hj')
    · obtain ⟨_, _, hm, _⟩ := Algo.send_climb (localInv_run hinit hh hr s) hj'; cases hm
    · obtain ⟨_, hm, _⟩ := Algo.send_propose_eq hj'; cases hm
    · obtain ⟨_, hm, _⟩ := Algo.send_voteProposal_eq hj'; cases hm
    · exact no_timeout_nullify hinit hh hb hs R s r hr j' hj'
    · -- 24〜28 行: 証拠の署名者に正直者はいない
      obtain ⟨hm, _, c₀, hc₀, hnp⟩ := Algo.send_nullifyNoProgress_eq hj'
      injection hm with _ hv4
      have hL4 := Algo.localInv_st4 (Δ := Δ) (lead := lead) (localInv_run hinit hh hr s)
      have hvote := hL4.notar_mem c₀ hc₀
      have hcv : c₀.view = v := (hL4.notar_view c₀ hc₀).trans hv4.symm
      -- c₀ は lead(v) のブロック
      have hc₀eq : c₀ = leaderBlockAt f lead s₀ instrs v e := by
        rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.S_st4_subset_st5 f Δ lead r _ hvote)
          with hm' | ⟨_, j'', hs''⟩
        · obtain ⟨s', _, j₃, hj₃⟩ := sendsBefore_of_mem_S hinit hm' rfl
            (Msg.vote_ne_gen_vote (by rw [hcv]; exact R.hv))
          exact vote_unique_leaderBlock hinit hh hb hs R s' r hr c₀ hcv j₃ hj₃
        · have hsend : Action.send (Msg.vote r c₀) j'' ∈ (instrs s).actions r := by
            rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd']
            exact List.mem_append_left _ hs''
          exact vote_unique_leaderBlock hinit hh hb hs R s r hr c₀ hcv j'' hsend
      rw [← hv4] at hnp
      obtain ⟨w, hw, hwc⟩ := exists_correct_of_lt_card hb (lt_of_lt_of_le (by omega) hnp)
      rcases mem_noProgressWitnesses.mp hw with hwn | ⟨b'', hb''v, hne, hwv⟩
      · -- 正直者 w の nullify(v)
        by_cases hwr : w = r
        · subst hwr
          rcases Algo.mem_S_st4_nullify hwn with hm' | hs''
          · obtain ⟨s', hs', j₃, hj₃⟩ := sendsBefore_of_mem_S hinit hm' rfl nofun
            exact ih s' hs' w hwc j₃ hj₃
          · exact no_timeout_nullify hinit hh hb hs R s w hwc w hs''
        · have hm' : Msg.nullify w v ∈ ((State.run s₀ instrs s).procs r).S := by
            rcases Algo.mem_S_stage_or f Δ lead r _ (Algo.S_st4_subset_st5 f Δ lead r _ hwn)
              with hm' | hsig
            · exact hm'
            · simp only [Msg.signer, Option.some.injEq] at hsig
              exact absurd hsig hwr
          obtain ⟨s', hs', j₃, hj₃⟩ := sendsBefore_of_mem_S hinit hm' rfl nofun
          exact ih s' hs' w hwc j₃ hj₃
      · -- 正直者 w の、lead(v) のブロック以外への票はない
        have hb''eq : b'' = leaderBlockAt f lead s₀ instrs v e := by
          rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.S_st4_subset_st5 f Δ lead r _ hwv)
            with hm' | ⟨hsig, j'', hs''⟩
          · obtain ⟨s', _, j₃, hj₃⟩ := sendsBefore_of_mem_S hinit hm' rfl
              (Msg.vote_ne_gen_vote (by rw [hb''v]; exact R.hv))
            exact vote_unique_leaderBlock hinit hh hb hs R s' w hwc b'' hb''v j₃ hj₃
          · simp only [Msg.signer, Option.some.injEq] at hsig
            subst hsig
            have hsend : Action.send (Msg.vote w b'') j'' ∈ (instrs s).actions w := by
              rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd']
              exact List.mem_append_left _ hs''
            exact vote_unique_leaderBlock hinit hh hb hs R s w hwc b'' hb''v j'' hsend
        exact hne (by rw [hb''eq, hc₀eq])
  rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd'] at hj
  rcases List.mem_append.mp hj with hj | hj
  · exact hinner j hj
  · rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.send_forwardNew_mem hj)
      with hm | ⟨_, j', hs'⟩
    · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hm rfl nofun
      exact ih s' hs' r hr j'' hj''
    · exact hinner j' hs'

/-- 正直者 r が view v を通過するスロット s では、そのとき lead(v) のブロックに投票するか、
    既に投票している。 -/
theorem vote_at_pass {r : Fin n} (hr : Correct s₀ instrs r) {s : Nat}
    (hs1 : (viewAt s₀ instrs r s).val ≤ v.val) (hs2 : v.val < (viewAt s₀ instrs r (s + 1)).val) :
    ∃ s' ≤ s, ∃ j, Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v e)) j
      ∈ (instrs s').actions r := by
  rw [viewAt_succ_eq hh hr s] at hs2
  obtain ⟨q, hLq, hqv, _, hcert, hnew, hqS, hqsend⟩ :=
    Algo.climb_pass (localInv_run hinit hh hr s) hs1 hs2
  have hqsucc : q.S ⊆ ((State.run s₀ instrs (s + 1)).procs r).S :=
    (Algo.S_subset_advanceOnce f r q).trans
      (hqS.trans ((Algo.S_st1_subset_st5 f Δ lead r _).trans (S_st5_subset_succ hh hr s)))
  have hN : ¬ Nullified f q.S v := by
    intro hN
    have hcard := card_le_of_byz hb (nullifiers q.S v)
      fun w hw => exists_byz_of_not_correct fun hwc => ?_
    · unfold Nullified at hN; omega
    · rcases hnew _ (mem_nullifiers.mp hw) with hm | ⟨_, hm, _⟩
      · obtain ⟨s', _, j, hj⟩ := sendsBefore_of_mem_S hinit hm rfl nofun
        exact no_nullify_v hinit hh hb hs R s' w hwc j hj
      · cases hm
  have hM : Algo.mNotarisedAt f q.S q.view ≠ [] := by
    rw [hqv]; exact hcert.resolve_left hN
  rcases hnot : q.notarised with _ | c
  · rcases hnl : q.nullified with _ | _
    · obtain ⟨b'', hb'', hsend⟩ := Algo.advanceOnce_vote_of r (by rw [hqv]; exact hN) hM hnot hnl
      have hsend' : Action.send (Msg.vote r b'') r ∈ (instrs s).actions r := by
        rw [hh s r (hr s), Algo.step_eq_stepPair, Algo.stepPair_snd']
        apply List.mem_append_left
        simp only [Algo.innerActs, List.mem_append]
        left; left; left; left
        exact hqsend _ _ hsend
      have hbv := (Algo.mem_mNotarisedAt hb'').1
      rw [hqv] at hbv
      have := vote_unique_leaderBlock hinit hh hb hs R s r hr b'' hbv r hsend'
      refine ⟨s, le_refl _, r, ?_⟩
      rw [← this]; exact hsend'
    · have hmem := hLq.null_mem hnl
      rw [hqv] at hmem
      obtain ⟨s', _, j, hj⟩ := sendsBefore_of_mem_S hinit (hqsucc hmem) rfl nofun
      exact absurd hj (no_nullify_v hinit hh hb hs R s' r hr j)
  · have hcv := (hLq.notar_view c hnot).trans hqv
    obtain ⟨s', hs', j, hj⟩ := sendsBefore_of_mem_S hinit (hqsucc (hLq.notar_mem c hnot)) rfl
      (Msg.vote_ne_gen_vote (by rw [hcv]; exact R.hv))
    have := vote_unique_leaderBlock hinit hh hb hs R s' r hr c hcv j hj
    refine ⟨s', Nat.lt_succ_iff.mp hs', j, ?_⟩
    rw [← this]; exact hj

/-- t + 2δ 以降に登りを view v で終える正直者は、そのスロットで 9〜11 行により投票するか、
    既に投票している。 -/
theorem vote_at_climb_end {r : Fin n} (hr : Correct s₀ instrs r) {s : Nat} (hT : t + 2 * δ ≤ s)
    (hst1v : (Algo.st1 f r ((State.run s₀ instrs s).procs r)).view = v) :
    ∃ s' ≤ s, ∃ j, Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v e)) j
      ∈ (instrs s').actions r := by
  have hvalid := leader_valid_at (r := r) hinit hh hb hs R (T := s) hT
  have hbLv := leaderBlockAt_view hinit hh hb hs R
  have hst1S : ((State.run s₀ instrs s).procs r).S
      ⊆ (Algo.st1 f r ((State.run s₀ instrs s).procs r)).S := Algo.S_subset_st1 f r _
  have hst2S : (Algo.st1 f r ((State.run s₀ instrs s).procs r)).S
      ⊆ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S := Algo.S_subset_propose f lead r _
  have hst2v : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view = v := by
    rw [Algo.st2_view, hst1v]
  have hL1 := Algo.localInv_st1 (localInv_run hinit hh hr s)
  have hclimb_send : ∀ m j, Action.send m j
      ∈ (Algo.climb f r (Algo.maxView ((State.run s₀ instrs s).procs r).S + 1)
          ((State.run s₀ instrs s).procs r)).2 →
      Action.send m j ∈ (instrs s).actions r := by
    intro m j hm
    rw [hh s r (hr s), Algo.step_eq_stepPair, Algo.stepPair_snd']
    apply List.mem_append_left
    simp only [Algo.innerActs, List.mem_append]
    left; left; left; left
    exact hm
  have huniq : ∀ b', b'.view = (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view →
      b'.signer = some (lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view) →
      containsBlock (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S b' →
      b' = leaderBlockAt f lead s₀ instrs v e := by
    intro b' hb'v hb's hb'
    rw [hst2v] at hb'v hb's
    have hc := containsBlock_mono
      ((Algo.S_st2_subset_st5 f Δ lead r _).trans (S_st5_subset_succ hh hr s)) hb'
    exact own_block_eq_of_send hinit hh R.hlc hc hb's (leader_proposes hinit hh hb hs R r)
      (by rw [hb'v, hbLv])
  have hvp2 : ValidProposal f lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S
      (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view
      (leaderBlockAt f lead s₀ instrs v e) :=
    ⟨by rw [hst2v]; exact hbLv, by rw [hst2v]; rfl,
      containsBlock_mono (hst1S.trans hst2S) hvalid.mem, huniq, Algo.leaderBlock_ne_gen _ _ _,
      fun p₀ hp₀ => (hvalid.parent p₀ hp₀).mono (hst1S.trans hst2S),
      fun p₀ hp₀ w h1 h2 =>
        (hvalid.gaps p₀ hp₀ w h1 (by rw [hst2v] at h2; exact h2)).mono (hst1S.trans hst2S)⟩
  have hprop : Algo.proposals lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S
      (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view
      = [leaderBlockAt f lead s₀ instrs v e] :=
    Algo.proposals_eq_singleton (containsBlock_mono (hst1S.trans hst2S) hvalid.mem)
      (by rw [hst2v]; rfl) (by rw [hst2v]; exact hbLv) huniq
  have h3 := Algo.voteProposal_eq_of_singleton (f := f) (i := r) hprop
  by_cases hcond : ValidProposal f lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S
      (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view
      (leaderBlockAt f lead s₀ instrs v e)
      ∧ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).notarised = none
      ∧ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).nullified = false
  · refine ⟨s, le_refl _, r, ?_⟩
    rw [hh s r (hr s), Algo.step_eq_stepPair, Algo.stepPair_snd']
    apply List.mem_append_left
    simp only [Algo.innerActs, List.mem_append]
    left; left; right
    rw [h3, if_pos hcond]
    exact Algo.mem_disseminate_snd.mpr ⟨r, rfl⟩
  · have hnn : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).notarised ≠ none
        ∨ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).nullified = true := by
      by_cases h1 : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).notarised = none
      · by_cases h2 : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).nullified = false
        · exact absurd ⟨hvp2, h1, h2⟩ hcond
        · right; simpa using h2
      · exact Or.inl h1
    have hn2 : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).notarised
        = (Algo.st1 f r ((State.run s₀ instrs s).procs r)).notarised :=
        Algo.propose_notarised f lead r _
    have hl2 : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).nullified
        = (Algo.st1 f r ((State.run s₀ instrs s).procs r)).nullified :=
        Algo.propose_nullified f lead r _
    rcases hnn with hnot | hnl
    · rw [hn2] at hnot
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hnot
      have hcv : c.view = v := (hL1.notar_view c hc).trans hst1v
      rcases Algo.mem_S_st1 (hL1.notar_mem c hc) with hm1 | ⟨b', hb', _, j, hj⟩
      · obtain ⟨s', hs', j, hj⟩ := sendsBefore_of_mem_S hinit hm1 rfl
          (Msg.vote_ne_gen_vote (by rw [hcv]; exact R.hv))
        have := vote_unique_leaderBlock hinit hh hb hs R s' r hr c hcv j hj
        refine ⟨s', hs'.le, j, ?_⟩
        rw [← this]; exact hj
      · injection hb' with _ hbb
        subst hbb
        have hj' := hclimb_send _ _ hj
        have := vote_unique_leaderBlock hinit hh hb hs R s r hr c hcv j hj'
        refine ⟨s, le_refl _, j, ?_⟩
        rw [← this]; exact hj'
    · rw [hl2] at hnl
      have hmem := hL1.null_mem hnl
      rw [hst1v] at hmem
      rcases Algo.mem_S_st1 hmem with hm1 | ⟨_, hb', _⟩
      · obtain ⟨s', _, j, hj⟩ := sendsBefore_of_mem_S hinit hm1 rfl nofun
        exact absurd hj (no_nullify_v hinit hh hb hs R s' r hr j)
      · cases hb'

/-- t + 2δ 以降のスロット s の終わりに view v 以上にいる正直者は、s までに lead(v) の
    ブロックに投票している。 -/
theorem vote_by {r : Fin n} (hr : Correct s₀ instrs r) {s : Nat} (hT : t + 2 * δ ≤ s)
    (hle : v.val ≤ (viewAt s₀ instrs r (s + 1)).val) :
    ∃ s' ≤ s, ∃ j, Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v e)) j
      ∈ (instrs s').actions r := by
  rcases Nat.lt_or_ge v.val (viewAt s₀ instrs r (s + 1)).val with hlt | hge
  · rcases Nat.lt_or_ge v.val (viewAt s₀ instrs r s).val with hlt' | hge'
    · obtain ⟨s'', hs'', h1, h2⟩ := exists_leave_slot hinit R.hv hlt'
      obtain ⟨s', hs', j, hj⟩ := vote_at_pass hinit hh hb hs R hr h1 h2
      exact ⟨s', by omega, j, hj⟩
    · exact vote_at_pass hinit hh hb hs R hr hge' hlt
  · have heq : (viewAt s₀ instrs r (s + 1)).val = v.val := le_antisymm hge hle
    have hst1v : (Algo.st1 f r ((State.run s₀ instrs s).procs r)).view = v := by
      rw [← viewAt_succ_eq hh hr s]; exact View.val_injective heq
    exact vote_at_climb_end hinit hh hb hs R hr hT hst1v

/-- 全正直者が lead(v) のブロックに投票する。 -/
theorem all_vote_leaderBlock (hn : 5 * f + 1 ≤ n) {r : Fin n} (hr : Correct s₀ instrs r) :
    Sends instrs r (Msg.vote r (leaderBlockAt f lead s₀ instrs v e)) := by
  obtain ⟨T, hT⟩ := progression hn hinit hh hb (hs.mono R.hδ) hr ⟨v.val + 1⟩
  obtain ⟨s, _, hs1, hs2⟩ := exists_leave_slot hinit R.hv (Nat.lt_of_succ_le hT)
  obtain ⟨s', _, j, hj⟩ := vote_at_pass hinit hh hb hs R hr hs1 hs2
  exact ⟨s', j, hj⟩

end CorrectLeader


/-- Lemma 5.6 の設定は、lead(v) が正直で最初の正直者が GST 以降に v に入れば作れる。 -/
theorem leader_round (hn : 5 * f + 1 ≤ n) (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ GST s₀ instrs)
    (hδ : δ ≤ Δ) {v : View} (hv : 1 ≤ v.val) (hi : Correct s₀ instrs (lead v)) {t : Nat}
    (hfirst : FirstEntry s₀ instrs v t) (hgst : GST.val ≤ t) :
    ∃ e, LeaderRound f Δ δ lead s₀ instrs GST v t e := by
  have hreach : ∃ s, v.val ≤ (viewAt s₀ instrs (lead v) (s + 1)).val :=
    ⟨t + δ, enter_all hinit hh hs hfirst hgst hi⟩
  obtain ⟨e, hev, hemin, hstart⟩ := entry_slot hinit hv hreach
  have he : e ≤ t + δ := by
    rcases Nat.lt_or_ge (t + δ) e with h | h
    · exact absurd (enter_all hinit hh hs hfirst hgst hi) (not_le.mpr (hemin (t + δ) h))
    · exact h
  exact ⟨e, ⟨hn, hδ, hv, hfirst, hgst, hi, he, hev, hemin, hstart⟩⟩

end Minimmit
