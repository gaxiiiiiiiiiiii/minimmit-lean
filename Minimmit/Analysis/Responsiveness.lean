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
  have hLN : LNotarised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S
      (leaderBlockAt f lead s₀ instrs v e) := by
    right
    refine (card_correctSet hb).trans (Finset.card_le_card fun r hr => ?_)
    have hrc := mem_correctSet.mp hr
    have hle : v.val ≤ (viewAt s₀ instrs r (t + 2 * δ + 1)).val :=
      (enter_all hinit hh hs hfirst hgst hrc).trans (viewAt_mono r (by omega))
    obtain ⟨s, hsT, j', hj'⟩ := vote_by hinit hh hb hs R hrc (s := t + 2 * δ) (le_refl _) hle
    have hj'' : Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v e)) j
        ∈ (instrs s).actions r := by
      rw [hh s r (hrc s)] at hj' ⊢
      exact Algo.send_all hj' j
    rw [mem_voters]
    exact delivered hinit hh hs hrc hj'' (by omega) (by omega)
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

/-- Lemma 5.9: 最初の正直者が t ≥ GST に view v に入るなら、lead(v) が正直かどうかに
    よらず、正直者は全員 t + 2Δ + 3δ までに view v を離れる。 -/
theorem leave_view (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ s₀ instrs) {v : View}
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : hs.GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j → v.val < (viewAt s₀ instrs j (t + 2 * Δ + 3 * δ + 1)).val := by
  sorry

/-- Lemma 5.10（Optimistic responsiveness）: 取引 tr を正直者が初めて受け取るのが t ≥ GST
    なら、正直者は全員 t + δ + (f_a + 1)(2Δ + 3δ) + 3δ までに tr を finalise する。
    どの f_a + 1 個の連続する view にも正直なリーダーがいることを仮定する（論文の
    lead(v) = p_{(v mod n)+1} は f_a 人以下の腐敗のもとでこれを満たす）。 -/
theorem optimistic_responsiveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ s₀ instrs) {fa : Nat} (hfa : ByzBound fa s₀ instrs)
    (hlead : ∀ v : View, ∃ v' : View, v.val ≤ v'.val ∧ v'.val ≤ v.val + fa
      ∧ Correct s₀ instrs (lead v'))
    {i : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {tr : Tx}
    (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S)
    (hfirst : ∀ j t', Correct s₀ instrs j → t' < t → Msg.tx tr ∉ ((State.run s₀ instrs t').procs j).S)
    (hgst : hs.GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j → ∃ b : Block Tx,
      LNotarised f ((State.run s₀ instrs (t + δ + (fa + 1) * (2 * Δ + 3 * δ) + 3 * δ)).procs j).S b
      ∧ tr ∈ b.trStar := by
  sorry

end Minimmit
