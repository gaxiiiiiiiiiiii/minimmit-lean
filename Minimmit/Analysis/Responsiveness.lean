import Minimmit.Analysis.Liveness

/-!
# Optimistic responsiveness（§5.3）

Lemma 5.8〜5.10。δ ≤ Δ は GST 以後の実際の遅延の上界、f_a ≤ f は実際に腐敗する人数。
論文の O(·) は、証明中の具体的な bound で置き換えている。

δ の仮定は `PartialSync δ`、つまり GST 前に送った packet も GST + δ までに届く。5.8 の
証明は、最初の正直者が証明書を転送した時刻が GST より前であっても、それが t + δ までに
全員へ届くことを使うので、この読みが要る。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-- Lemma 5.8 の核: 全正直者の票が t + 2δ までに出て t + 3δ までに届く。 -/
theorem leaderBlock_lnotarised_by (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs) (hs : PartialSync δ s₀ instrs)
    {v : View} {t e : Nat} (R : LeaderRound f Δ δ lead s₀ instrs hs v t e) {j : Fin n}
    (hj : Correct s₀ instrs j) :
    LNotarised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S (leaderBlockAt f lead s₀ instrs v e) := by
  have hδ1 := hs.one_le
  have hgst := R.hgst
  right
  refine (card_correctSet hb).trans (Finset.card_le_card fun r hr => ?_)
  have hrc := mem_correctSet.mp hr
  have hle : v.val ≤ (viewAt s₀ instrs r (t + 2 * δ + 1)).val :=
    (enter_all hinit hh hs R.hfirst R.hgst hrc).trans (viewAt_mono r (by omega))
  obtain ⟨s, hsT, j', hj'⟩ := vote_by hinit hh hb hs R hrc (s := t + 2 * δ) (le_refl _) hle
  have hj'' : Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v e)) j
      ∈ (instrs s).actions r := by
    rw [hh s r (hrc s)] at hj' ⊢
    exact Algo.send_all hj' j
  rw [mem_voters]
  exact delivered hinit hh hs hrc hj'' (by omega) (by omega)

/-- Lemma 5.8: lead(v) が正直で、最初の正直者が t ≥ GST に view v に入るなら、正直者は
    全員 t + 3δ までに view v のブロックを finalise し、view v を離れる。 -/
theorem correct_leader_finalises_fast (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ s₀ instrs) {v : View} (hv : 1 ≤ v.val)
    (hi : Correct s₀ instrs (lead v))
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : hs.GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j →
      (∃ b : Block Tx, b.view = v ∧ LNotarised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S b)
      ∧ v.val < (viewAt s₀ instrs j (t + 3 * δ + 1)).val := by
  intro j hj
  have hδ1 := hs.one_le
  obtain ⟨e, R⟩ := leader_round hinit hh hs hδ hv hi hfirst hgst
  have hbLv := leaderBlockAt_view hinit hh hb hs R
  have hLN := leaderBlock_lnotarised_by hn hinit hh hb hs R hj
  refine ⟨⟨leaderBlockAt f lead s₀ instrs v e, hbLv, hLN⟩, ?_⟩
  have hM : MNotarised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S
      (leaderBlockAt f lead s₀ instrs v e) := by
    rcases hLN with h | h
    · exact Or.inl h
    · right; omega
  have hcert : Algo.HasCert f ((State.run s₀ instrs (t + 3 * δ)).procs j).S v := by
    rw [← hbLv]
    exact Algo.hasCert_of_mnotarised (Algo.leaderBlock_ne_gen _ _) hM
  have henter := enter_all hinit hh hs hfirst hgst hj
  rcases lt_trichotomy (viewAt s₀ instrs j (t + 3 * δ)).val v.val with hlt | heq | hgt
  · exfalso
    have := viewAt_mono (s₀ := s₀) (instrs := instrs) j (show t + δ + 1 ≤ t + 3 * δ by omega)
    omega
  · exact leave_of_hasCert hh hj (View.val_injective heq) hcert
  · exact lt_of_lt_of_le hgt (viewAt_le_succ j _)

/-- 正直者が期限までに view v の証明書を持てば、正直者は全員その次のスロットには v を
    離れている。 -/
theorem leave_all_of_cert (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ s₀ instrs) {r : Fin n} (hr : Correct s₀ instrs r) {s : Nat} {v : View}
    (hv : 1 ≤ v.val) (hc : Algo.HasCert f ((State.run s₀ instrs s).procs r).S v) {T : Nat}
    (hT₁ : s + 1 ≤ T) (hT₂ : max hs.GST.val s + δ ≤ T)
    (henter : ∀ j, Correct s₀ instrs j → v.val ≤ (viewAt s₀ instrs j T).val) :
    ∀ j, Correct s₀ instrs j → v.val < (viewAt s₀ instrs j (T + 1)).val := by
  intro j hj
  have hcert := hasCert_all hinit hh hs hr hv hc hj hT₁ hT₂
  rcases lt_or_eq_of_le (henter j hj) with hgt | heq
  · exact lt_of_lt_of_le hgt (viewAt_le_succ j T)
  · exact leave_of_hasCert hh hj (View.val_injective heq.symm) hcert

/-- Lemma 5.9 の一般形: 最初の正直者が t に view v に入るなら、lead(v) が正直かどうかに
    よらず、正直者は全員 max(t, GST) + 2Δ + 3δ までに view v を離れる。T₀ は t 以上で
    GST 以上の任意の時刻。 -/
theorem leave_view_anchor (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ s₀ instrs) {v : View} (hv : 1 ≤ v.val)
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) {T₀ : Nat} (ht : t ≤ T₀)
    (hgst : hs.GST.val ≤ T₀) :
    ∀ j, Correct s₀ instrs j → v.val < (viewAt s₀ instrs j (T₀ + 2 * Δ + 3 * δ + 1)).val := by
  classical
  have hδ1 := hs.one_le
  have hΔ1 : 1 ≤ Δ := le_trans hδ1 hδ
  have henter : ∀ r, Correct s₀ instrs r → v.val ≤ (viewAt s₀ instrs r (T₀ + δ + 1)).val :=
    fun r hr => enter_all_anchor hinit hh hs hfirst ht hgst hr
  have henterT : ∀ r, Correct s₀ instrs r →
      v.val ≤ (viewAt s₀ instrs r (T₀ + 2 * Δ + 3 * δ)).val :=
    fun r hr => (henter r hr).trans (viewAt_mono r (by omega))
  by_cases hcert : ∃ r, Correct s₀ instrs r ∧ ∃ s ≤ T₀ + 2 * Δ + 2 * δ,
      Algo.HasCert f ((State.run s₀ instrs s).procs r).S v
  · -- 証明書が転送されて全員が離れる
    obtain ⟨r, hr, s, hsT, hc⟩ := hcert
    exact leave_all_of_cert hinit hh hs hr hv hc (by omega) (by omega) henterT
  have hnc : ∀ r, Correct s₀ instrs r → ∀ s, s ≤ T₀ + 2 * Δ + 2 * δ →
      ¬ Algo.HasCert f ((State.run s₀ instrs s).procs r).S v :=
    fun r hr s hsT hc => hcert ⟨r, hr, s, hsT, hc⟩
  -- 全正直者は t + 2Δ + 2δ + 1 まで view v 以下
  have hstay : ∀ r, Correct s₀ instrs r → ∀ s, s ≤ T₀ + 2 * Δ + 2 * δ + 1 →
      (viewAt s₀ instrs r s).val ≤ v.val := by
    intro r hr s hsT
    by_contra hlt
    have hlt := not_le.mp hlt
    obtain ⟨s', hs', h1, h2⟩ := exists_leave_slot hinit hv hlt
    rw [viewAt_succ_eq hh hr s'] at h2
    exact hnc r hr s' (by omega) (Algo.st1_certs h1 h2)
  have hview : ∀ r, Correct s₀ instrs r → ∀ s, T₀ + δ + 1 ≤ s → s ≤ T₀ + 2 * Δ + 2 * δ + 1 →
      viewAt s₀ instrs r s = v :=
    fun r hr s h1 h2 =>
      View.val_injective (le_antisymm (hstay r hr s h2) ((henter r hr).trans (viewAt_mono r h1)))
  -- T₀ + δ + 2Δ までに投票か nullify
  have hto : ∀ r, Correct s₀ instrs r →
      (∃ b, b.view = v ∧ Msg.vote r b ∈ ((State.run s₀ instrs (T₀ + δ + 2 * Δ + 1)).procs r).S)
        ∨ Msg.nullify r v ∈ ((State.run s₀ instrs (T₀ + δ + 2 * Δ + 1)).procs r).S := by
    intro r hr
    obtain ⟨e, hev, hemin, hstart⟩ := entry_slot hinit hv ⟨T₀ + δ, henter r hr⟩
    have he : e ≤ T₀ + δ := by
      rcases Nat.lt_or_ge (T₀ + δ) e with h | h
      · exact absurd (henter r hr) (not_le.mpr (hemin _ h))
      · exact h
    have hte : t ≤ e := hfirst.first r e hr hev
    have hview' : ∀ s, e + 1 ≤ s → s ≤ T₀ + 2 * Δ + 2 * δ + 1 → viewAt s₀ instrs r s = v :=
      fun s h1 h2 => View.val_injective (le_antisymm (hstay r hr s h2) (hev.trans (viewAt_mono r h1)))
    have htimer : timerAt s₀ instrs r (e + 2 * Δ) = 2 * Δ := by
      rcases hstart with hlt | ⟨rfl, hv1⟩
      · have h1 : timerAt s₀ instrs r (e + 1) = 1 := by
          rcases timerAt_succ (s₀ := s₀) (instrs := instrs) r e with ⟨h, _⟩ | ⟨_, h⟩
          · exact h
          · exfalso; rw [h] at hev; omega
        have hst : ∀ k' ≤ 2 * Δ - 1,
            viewAt s₀ instrs r (e + 1 + k') = viewAt s₀ instrs r (e + 1) := by
          intro k' hk'
          rw [hview' (e + 1 + k') (by omega) (by omega), hview' (e + 1) (le_refl _) (by omega)]
        have := timerAt_add (s₀ := s₀) (instrs := instrs) r (e + 1) (2 * Δ - 1) hst
        rw [h1] at this
        rw [show e + 2 * Δ = e + 1 + (2 * Δ - 1) by omega, this]
        omega
      · have h0 : timerAt s₀ instrs r 0 = 0 := by
          show ((State.run s₀ instrs 0).procs r).timer = 0
          rw [State.run, hinit.procs]; rfl
        have hst : ∀ k' ≤ 2 * Δ, viewAt s₀ instrs r (0 + k') = viewAt s₀ instrs r 0 := by
          intro k' hk'
          apply View.val_injective
          rw [viewAt_zero hinit]
          have h1 := hstay r hr (0 + k') (by omega)
          have h2 := viewAt_pos hinit hh hr (0 + k')
          omega
        have := timerAt_add (s₀ := s₀) (instrs := instrs) r 0 (2 * Δ) hst
        rw [h0] at this
        simpa using this
    have hvT : viewAt s₀ instrs r (e + 2 * Δ) = v := hview' _ (by omega) (by omega)
    rcases timeout hinit hh hr hvT htimer with h | h | h
    · obtain ⟨b, hbv, hm⟩ := h
      exact Or.inl ⟨b, hbv, S_subset_run s₀ instrs r (by omega) hm⟩
    · exact Or.inr (S_subset_run s₀ instrs r (by omega) h)
    · exfalso
      have := hstay r hr (e + 2 * Δ + 1) (by omega)
      omega
  -- t + 2Δ + 2δ には全正直者の投票か nullify が全正直者に届いている
  have hmsg : ∀ r, Correct s₀ instrs r → ∀ r', Correct s₀ instrs r' →
      (∃ b, b.view = v ∧ Msg.vote r b ∈ ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r').S)
        ∨ Msg.nullify r v ∈ ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r').S := by
    intro r hr r' hr'
    rcases hto r hr with ⟨b, hbv, hm⟩ | hm
    · exact Or.inl ⟨b, hbv, own_delivered hinit hh hs hr' hr hm rfl (by omega) (by omega)⟩
    · exact Or.inr (own_delivered hinit hh hs hr' hr hm rfl (by omega) (by omega))
  -- 全正直者が t + 2Δ + 2δ + 1 までに nullify(v) を送る
  have hnull : ∀ r, Correct s₀ instrs r →
      Msg.nullify r v ∈ ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ + 1)).procs r).S := by
    intro r hr
    rcases hto r hr with ⟨b, hbv, hm⟩ | hm
    · have hvT : viewAt s₀ instrs r (T₀ + 2 * Δ + 2 * δ) = v := hview r hr _ (by omega) (by omega)
      have hmT : Msg.vote r b ∈ ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S :=
        S_subset_run s₀ instrs r (by omega) hm
      have hL := localInv_run hinit hh hr (T₀ + 2 * Δ + 2 * δ)
      have hnot : ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).notarised = some b := by
        refine ((hL.notar b hmT).2.resolve_left ?_).2
        rw [hbv]
        change ¬ v.val < (viewAt s₀ instrs r (T₀ + 2 * Δ + 2 * δ)).val
        rw [hvT]; exact lt_irrefl _
      have hg : b ≠ .gen := by
        intro h; subst h
        have : v.val = 0 := by rw [← hbv]; rfl
        omega
      have hnoM : ¬ MNotarised f ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S b := by
        intro hM
        apply hnc r hr (T₀ + 2 * Δ + 2 * δ) (le_refl _)
        rw [← hbv]
        exact Algo.hasCert_of_mnotarised hg hM
      have hvoters : (voters ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S b).card ≤ 2 * f := by
        by_contra h
        exact hnoM (Or.inr (not_le.mp h))
      have hnp : NoProgress f ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S v (some b) := by
        have hCsub : correctSet s₀ instrs ⊆
            (correctSet s₀ instrs).filter
              (fun c => NoProgressWitness ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S
                v (some b) c)
            ∪ (correctSet s₀ instrs).filter
              (fun c => Msg.vote c b ∈ ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S) := by
          intro c hc
          rcases hmsg c (mem_correctSet.mp hc) r hr with ⟨b', hb'v, hm'⟩ | hm'
          · by_cases hbb : b' = b
            · subst hbb
              exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc, hm'⟩)
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
                ⟨hc, .vote b' hb'v (fun h => hbb (Option.some.inj h)) hm'⟩)
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, .nullify hm'⟩)
        have hV : ((correctSet s₀ instrs).filter
            (fun c => Msg.vote c b ∈ ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S)).card
            ≤ 2 * f :=
          (Finset.card_le_card fun c hc => mem_voters.mpr (Finset.mem_filter.mp hc).2).trans hvoters
        have hW : (correctSet s₀ instrs).filter
            (fun c => NoProgressWitness ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S
              v (some b) c)
            ⊆ noProgressWitnesses ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S v (some b) :=
          fun c hc => mem_noProgressWitnesses.mpr (Finset.mem_filter.mp hc).2
        have h1 := Finset.card_le_card hCsub
        have h2 := Finset.card_union_le ((correctSet s₀ instrs).filter
            (fun c => NoProgressWitness ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S
              v (some b) c))
          ((correctSet s₀ instrs).filter
            (fun c => Msg.vote c b ∈ ((State.run s₀ instrs (T₀ + 2 * Δ + 2 * δ)).procs r).S))
        have h4 := Finset.card_le_card hW
        have hC := card_correctSet (s₀ := s₀) (instrs := instrs) hb
        unfold NoProgress
        omega
      rcases noprogress_reaction hinit hh hr hvT hnot hnp with h | h
      · exact h
      · exfalso
        have := hstay r hr (T₀ + 2 * Δ + 2 * δ + 1) (le_refl _)
        omega
    · exact S_subset_run s₀ instrs r (by omega) hm
  -- nullification が全員に届き、全員が離れる
  intro j hj
  have hN : Nullified f ((State.run s₀ instrs (T₀ + 2 * Δ + 3 * δ)).procs j).S v := by
    have hsub : correctSet s₀ instrs
        ⊆ nullifiers ((State.run s₀ instrs (T₀ + 2 * Δ + 3 * δ)).procs j).S v :=
      fun r hr => mem_nullifiers.mpr (own_delivered hinit hh hs hj (mem_correctSet.mp hr)
        (hnull r (mem_correctSet.mp hr)) rfl (by omega) (by omega))
    have := Finset.card_le_card hsub
    have hC := card_correctSet (s₀ := s₀) (instrs := instrs) hb
    unfold Nullified
    omega
  rcases lt_or_eq_of_le (henterT j hj) with hgt | heq
  · exact lt_of_lt_of_le hgt (viewAt_le_succ j _)
  · exact leave_of_nullified hh hj (View.val_injective heq.symm) hN

/-- Lemma 5.9: 最初の正直者が t ≥ GST に view v に入るなら、lead(v) が正直かどうかに
    よらず、正直者は全員 t + 2Δ + 3δ までに view v を離れる。 -/
theorem leave_view (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ s₀ instrs) {v : View} (hv : 1 ≤ v.val)
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : hs.GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j → v.val < (viewAt s₀ instrs j (t + 2 * Δ + 3 * δ + 1)).val :=
  leave_view_anchor hn hinit hh hb hδ hs hv hfirst (le_refl t) hgst

/-- Lemma 5.10（Optimistic responsiveness）: 取引 tr を正直者が初めて受け取るのが t ≥ GST
    なら、正直者は全員 t + δ + (f_a + 1)(2Δ + 3δ) + 3δ までに tr を finalise する。
    どの f_a + 1 個の連続する view にも正直なリーダーがいることを仮定する（論文の
    lead(v) = p_{(v mod n)+1} は f_a 人以下の腐敗のもとでこれを満たす）。 -/
theorem optimistic_responsiveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ s₀ instrs) {fa : Nat}
    (hlead : ∀ v : View, ∃ v' : View, v.val ≤ v'.val ∧ v'.val ≤ v.val + fa
      ∧ Correct s₀ instrs (lead v'))
    {i : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {tr : Tx}
    (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S)
    (hfirst : ∀ j t', Correct s₀ instrs j → t' < t → Msg.tx tr ∉ ((State.run s₀ instrs t').procs j).S)
    (hgst : hs.GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j → ∃ b : Block Tx,
      LNotarised f ((State.run s₀ instrs (t + δ + (fa + 1) * (2 * Δ + 3 * δ) + 3 * δ)).procs j).S b
      ∧ tr ∈ b.trStar := by
  classical
  have hδ1 := hs.one_le
  have hΔ1 : 1 ≤ Δ := le_trans hδ1 hδ
  -- tr は t + δ までに全正直者に届く
  have htx : ∀ r, Correct s₀ instrs r → ∀ T, t + δ ≤ T →
      Msg.tx tr ∈ ((State.run s₀ instrs T).procs r).S := fun r hr T hT =>
    delivered hinit hh hs hi (tx_forwarded hinit hh hi htr (fun t' ht' => hfirst i t' hi ht') r)
      (by omega) (by omega)
  -- v₀: t + δ における正直者の view の最大
  have hne : (correctSet s₀ instrs).Nonempty := ⟨i, mem_correctSet.mpr hi⟩
  obtain ⟨r₀, hr₀, hv₀⟩ := Finset.exists_mem_eq_sup (correctSet s₀ instrs) hne
    (fun r => (viewAt s₀ instrs r (t + δ)).val)
  have hr₀c := mem_correctSet.mp hr₀
  set v₀ : View := ⟨(correctSet s₀ instrs).sup fun r => (viewAt s₀ instrs r (t + δ)).val⟩ with hv₀def
  have hbound : ∀ r, Correct s₀ instrs r → (viewAt s₀ instrs r (t + δ)).val ≤ v₀.val :=
    fun r hr => Finset.le_sup (f := fun r => (viewAt s₀ instrs r (t + δ)).val) (mem_correctSet.mpr hr)
  have hv₀1 : 1 ≤ v₀.val := le_trans (viewAt_pos hinit hh hi (t + δ)) (hbound i hi)
  have hv₀r : v₀.val = (viewAt s₀ instrs r₀ (t + δ)).val := hv₀
  have hreach₀ : ∃ s, ∃ r, Correct s₀ instrs r ∧ v₀.val ≤ (viewAt s₀ instrs r (s + 1)).val :=
    ⟨t + δ - 1, r₀, hr₀c, by rw [show t + δ - 1 + 1 = t + δ by omega, hv₀r]⟩
  -- v₀ + k の最初の入場は t + δ + k(2Δ + 3δ) 以前
  have hP : ∀ k, ∃ tk, FirstEntry s₀ instrs ⟨v₀.val + k⟩ tk ∧ tk ≤ t + δ + k * (2 * Δ + 3 * δ) := by
    intro k
    induction k with
    | zero =>
      refine ⟨Nat.find hreach₀, ⟨?_, ?_⟩, ?_⟩
      · obtain ⟨r, hr, h⟩ := Nat.find_spec hreach₀
        exact ⟨r, hr, h⟩
      · intro r t' hr h
        exact Nat.find_min' hreach₀ ⟨r, hr, h⟩
      · have := Nat.find_min' hreach₀ ⟨r₀, hr₀c,
          by rw [show t + δ - 1 + 1 = t + δ by omega, hv₀r]⟩
        omega
    | succ k ih =>
      obtain ⟨tk, hfk, hle⟩ := ih
      have hleave := leave_view_anchor hn hinit hh hb hδ hs (v := ⟨v₀.val + k⟩)
        (show 1 ≤ v₀.val + k by omega) hfk (T₀ := t + δ + k * (2 * Δ + 3 * δ)) hle (by omega)
      have hreach : ∃ s, ∃ r, Correct s₀ instrs r
          ∧ (⟨v₀.val + (k + 1)⟩ : View).val ≤ (viewAt s₀ instrs r (s + 1)).val := by
        refine ⟨t + δ + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ, i, hi, ?_⟩
        have h1 : v₀.val + k < (viewAt s₀ instrs i
            (t + δ + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ + 1)).val := hleave i hi
        show v₀.val + (k + 1) ≤ _
        omega
      refine ⟨Nat.find hreach, ⟨Nat.find_spec hreach, fun r t' hr h => Nat.find_min' hreach ⟨r, hr, h⟩⟩, ?_⟩
      have h1 := Nat.find_min' hreach (m := t + δ + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ) ⟨i, hi, by
        have h1 : v₀.val + k < (viewAt s₀ instrs i
            (t + δ + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ + 1)).val := hleave i hi
        show v₀.val + (k + 1) ≤ _
        omega⟩
      rw [Nat.add_mul, Nat.one_mul]
      omega
  -- v₁: v₀ + 1 以上 v₀ + 1 + f_a 以下の、正直なリーダーの view
  obtain ⟨v₁, hv₁ge, hv₁le, hlc⟩ := hlead ⟨v₀.val + 1⟩
  have hv₁ge' : v₀.val + 1 ≤ v₁.val := hv₁ge
  have hv₁le' : v₁.val ≤ v₀.val + 1 + fa := hv₁le
  obtain ⟨tm, hfm, hlem⟩ := hP (v₁.val - v₀.val)
  have hv₁eq : (⟨v₀.val + (v₁.val - v₀.val)⟩ : View) = v₁ :=
    View.val_injective (by show v₀.val + (v₁.val - v₀.val) = v₁.val; omega)
  rw [hv₁eq] at hfm
  have hv₁1 : 1 ≤ v₁.val := by omega
  -- v₁ への最初の入場は t + δ 以降
  have htm : t + δ ≤ tm := by
    obtain ⟨r, hr, h⟩ := hfm.entered
    by_contra hlt
    have h1 := viewAt_mono (s₀ := s₀) (instrs := instrs) r (show tm + 1 ≤ t + δ by omega)
    have h2 := hbound r hr
    omega
  obtain ⟨e, R⟩ := leader_round hinit hh hs hδ hv₁1 hlc hfm (by omega)
  have hte := t_le_e hinit hh hb hs R
  have hmul : (v₁.val - v₀.val) * (2 * Δ + 3 * δ) ≤ (fa + 1) * (2 * Δ + 3 * δ) :=
    Nat.mul_le_mul_right _ (by omega)
  intro j hj
  refine ⟨leaderBlockAt f lead s₀ instrs v₁ e, ?_, ?_⟩
  · exact (leaderBlock_lnotarised_by hn hinit hh hb hs R hj).mono
      (S_subset_run s₀ instrs j (by omega))
  · apply mem_trStar_leaderBlock
    apply Algo.S_subset_st1 f (lead v₁) _
    exact htx (lead v₁) hlc e (by omega)

end Minimmit
