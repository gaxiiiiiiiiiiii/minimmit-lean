import Minimmit.Analysis.Liveness.LeaderRound
import Minimmit.Analysis.Liveness.Finalise

/-!
# Lemma 5.8（Fast finalisation under a correct leader）

δ ≤ Δ は GST 以後の実際の遅延の上界、f_a ≤ f は実際に腐敗する人数。
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

/-- lead(v) のブロックは t + 3δ までに全正直者が finalise する: L-notarisation に加えて、
    親の M-notarisation が t + 2δ までに全員に届いているので、祖先は t + 3δ までに届く。 -/
theorem leaderBlock_finalised_by (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs) (hs : PartialSync δ GST s₀ instrs)
    {v : View} {t e : Nat} (R : LeaderRound f Δ δ lead s₀ instrs GST v t e) {j : Fin n} :
    Finalised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S
    (leaderBlockAt f lead s₀ instrs v e) := by
  have hn := R.hn
  have hδ1 := hs.one_le
  have hgst := R.hgst
  have hLN := leaderBlock_lnotarised_by (j := j) hinit hh hb hs R
  refine ⟨hLN, fun a ha => ?_⟩
  rcases ha.eq_or_parent with rfl | ⟨p, hp, hap⟩
  · obtain ⟨w, hw⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega) (show n - f ≤ _ from hLN))
    exact ⟨_, mem_voters.mp hw, rfl⟩
  · have hpar : (leaderBlockAt f lead s₀ instrs v e).parent
        = some (leaderParentAt f lead s₀ instrs v e) := rfl
    rw [hpar, Option.mem_some_iff] at hp
    subst hp
    have hMp := leader_parent_mnotarised_all (r := j) (T := t + 2 * δ) hinit hh hs R (le_refl _)
    exact ancestors_delivered hinit hh hb hs hMp (by omega) (by omega) a hap

/-- Lemma 5.8: lead(v) が正直で、最初の正直者が t ≥ GST に view v に入るなら、正直者は
    全員 t + 3δ までに view v のブロックを finalise し、view v を離れる。 -/
theorem correct_leader_finalises_fast (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ GST s₀ instrs) {v : View} (hv : 1 ≤ v.val)
    (hi : Correct s₀ instrs (lead v))
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j →
      (∃ b : Block n Tx, b.view = v ∧ Finalised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S b)
      ∧ v.val < (viewAt s₀ instrs j (t + 3 * δ + 1)).val := by
  intro j hj
  have hδ1 := hs.one_le
  obtain ⟨e, R⟩ := leader_round hn hinit hh hs hδ hv hi hfirst hgst
  have hbLv := leaderBlockAt_view hinit hh hb hs R
  have hLN := leaderBlock_lnotarised_by (j := j) hinit hh hb hs R
  refine ⟨⟨leaderBlockAt f lead s₀ instrs v e, hbLv,
    leaderBlock_finalised_by (j := j) hinit hh hb hs R⟩, ?_⟩
  have hM : MNotarised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S
      (leaderBlockAt f lead s₀ instrs v e) := by
    have h := hLN; unfold LNotarised at h; unfold MNotarised; omega
  have hcert : Algo.HasCert f ((State.run s₀ instrs (t + 3 * δ)).procs j).S v := by
    rw [← hbLv]
    exact Algo.hasCert_of_mnotarised hM
  have henter := enter_all hinit hh hs hfirst hgst hj
  rcases lt_trichotomy (viewAt s₀ instrs j (t + 3 * δ)).val v.val with hlt | heq | hgt
  · exfalso
    have := viewAt_mono (s₀ := s₀) (instrs := instrs) j (show t + δ + 1 ≤ t + 3 * δ by omega)
    omega
  · exact leave_of_hasCert hh hj (View.val_injective heq) hcert
  · exact lt_of_lt_of_le hgt (viewAt_le_succ j _)

end Minimmit
