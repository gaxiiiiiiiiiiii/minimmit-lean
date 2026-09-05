import Minimmit.Analysis.Liveness.LeaderRound

/-!
# Lemma 5.8（Fast finalisation under a correct leader）

δ ≤ Δ は GST 以後の実際の遅延の上界、f_a ≤ f は実際に腐敗する人数。

## 論文からの差異

- δ は `PartialSync δ` として与える。つまり GST 前に送った packet も GST + δ までに届く。
  証明は、最初の正直者が証明書を転送した時刻が GST より前であっても、それが t + δ までに
  全員へ届くことを使うので、この読みが要る。timeout の 2Δ は `Honest` の Δ のまま。
- 論文の主張の O(·) は具体的な上界 t + 3δ に置き換える。t + 3δ は論文の証明本文が出す数字で、
  証明の末尾は「receive b together with an L-notarisation … by t + 3δ, and also leave view v
  by this time」。具体的な上界は O(·) の主張を含む。
- view v ≥ 1 を仮定に持つ。論文の view は ℕ≥1 で、v = 0 では結論が成り立たない。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {GST : Time} {lead : View → Fin n} {s₀ : State n Tx}
  {instrs : Nat → Instr n Tx}

/-- Lemma 5.8 の核: 全正直者の票が t + 2δ までに出て t + 3δ までに届く。 -/
theorem leaderBlock_lnotarised_by (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs) (hs : PartialSync δ GST s₀ instrs)
    {v : View} {t e : Nat} (R : LeaderRound f Δ δ lead s₀ instrs GST v t e) {j : Fin n} :
    LNotarised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S
    (leaderBlockAt f lead s₀ instrs v e) := by
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
    (hδ : δ ≤ Δ) (hs : PartialSync δ GST s₀ instrs) {v : View} (hv : 1 ≤ v.val)
    (hi : Correct s₀ instrs (lead v))
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j →
      (∃ b : Block Tx, b.view = v ∧ LNotarised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S b)
      ∧ v.val < (viewAt s₀ instrs j (t + 3 * δ + 1)).val := by
  intro j hj
  have hδ1 := hs.one_le
  obtain ⟨e, R⟩ := leader_round hinit hh hs hδ hv hi hfirst hgst
  have hbLv := leaderBlockAt_view hinit hh hb hs R
  have hLN := leaderBlock_lnotarised_by (j := j) hinit hh hb hs R
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

end Minimmit
