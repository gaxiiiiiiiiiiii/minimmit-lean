import Minimmit.Analysis.Liveness.LeaderRound
import Minimmit.Analysis.Liveness.Finalise

/-!
# Lemma 5.7（Liveness）
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {GST : Time} {lead : View → Fin n} {s₀ : State n Tx}
  {instrs : Nat → Instr n Tx}

/-- Lemma 5.7（Liveness）: 正直者 p_i が受け取った取引は、あるスロットで任意の p_j が
    finalise したブロックの Tr* に入る。 -/
theorem liveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hs : PartialSync Δ GST s₀ instrs) (hlead : Fair lead)
    {i j : Fin n} (hi : Correct s₀ instrs i)
    {t : Nat} {tr : Tx} (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S) :
    ∃ t' b, Finalised f ((State.run s₀ instrs t').procs j).S b ∧ tr ∈ b.trStar := by
  classical
  have hΔ := hs.one_le
  -- max(GST, t) より後に始まる view v' で lead v' = i
  obtain ⟨v', hv'V, hlv'⟩ := hlead i
    ⟨(Finset.univ.sup fun r => (viewAt s₀ instrs r (max GST.val t + 1)).val) + 1⟩
  have hbound : ∀ r, (viewAt s₀ instrs r (max GST.val t + 1)).val < v'.val := fun r =>
    lt_of_lt_of_le (Nat.lt_succ_of_le
      (Finset.le_sup (f := fun r => (viewAt s₀ instrs r (max GST.val t + 1)).val)
        (Finset.mem_univ r))) hv'V
  have hv'1 : 1 ≤ v'.val := le_trans (Nat.succ_le_succ (Nat.zero_le _)) hv'V
  have hreach : ∃ s, ∃ r, Correct s₀ instrs r ∧ v'.val ≤ (viewAt s₀ instrs r (s + 1)).val := by
    obtain ⟨s, hs'⟩ := reaches_view hn hinit hh hb hs hi v'
    exact ⟨s, i, hi, hs'.trans (viewAt_le_succ i s)⟩
  have hfirst : FirstEntry s₀ instrs v' (Nat.find hreach) := firstEntry_of_reach hinit hv'1 hreach
  have hgst : max GST.val t < Nat.find hreach := by
    obtain ⟨r, hr, h⟩ := Nat.find_spec hreach
    by_contra hle
    have h1 := viewAt_mono (s₀ := s₀) (instrs := instrs) r (Nat.add_le_add_right (not_lt.mp hle) 1)
    have h2 := hbound r
    omega
  have hlc : Correct s₀ instrs (lead v') := hlv' ▸ hi
  obtain ⟨e, R⟩ := leader_round hn hinit hh hs (le_refl Δ) hv'1 hlc hfirst (by omega)
  have hte := first_entry_le_leader_entry hinit R
  -- 取引はブロックの Tr* に入る
  have htr' : tr ∈ (leaderBlockAt f lead s₀ instrs v' e).trStar := by
    apply mem_trStar_leaderBlock
    apply Algo.S_subset_st1 f (lead v') _
    rw [hlv']
    exact S_subset_run s₀ instrs i (by omega) htr
  -- 全正直者の票が j に届く
  have hvotes : ∀ r ∈ correctSet s₀ instrs, ∃ s, ∃ j',
      Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v' e)) j' ∈ (instrs s).actions r :=
    fun r hr => all_vote_leaderBlock hinit hh hb hs R hn (mem_correctSet.mp hr)
  obtain ⟨T, hT⟩ := exists_bound hvotes
  have hLN : LNotarised f ((State.run s₀ instrs (T + GST.val + Δ + 1)).procs j).S
      (leaderBlockAt f lead s₀ instrs v' e) := by
    refine (card_correctSet hb).trans (Finset.card_le_card fun r hr => ?_)
    obtain ⟨s, hsT, j', hj'⟩ := hT r hr
    have hrc := mem_correctSet.mp hr
    have hj'' : Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v' e)) j
        ∈ (instrs s).actions r := by
      rw [hh s r (hrc s)] at hj' ⊢
      exact Algo.send_all hj' j
    rw [mem_voters]
    exact delivered hinit hh hs hrc hj'' (by omega) (by omega)
  refine ⟨T + GST.val + Δ + 1 + (Nat.find hreach + 3 * Δ), leaderBlockAt f lead s₀ instrs v' e,
    ⟨hLN.mono (S_subset_run s₀ instrs j (by omega)), fun a ha => ?_⟩, htr'⟩
  rcases ha.eq_or_parent with rfl | ⟨p, hp, hap⟩
  · obtain ⟨w, hw⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega) (show n - f ≤ _ from hLN))
    exact ⟨_, S_subset_run s₀ instrs j (by omega) (mem_voters.mp hw), rfl⟩
  · have hpar : (leaderBlockAt f lead s₀ instrs v' e).parent
        = some (leaderParentAt f lead s₀ instrs v' e) := rfl
    rw [hpar, Option.mem_some_iff] at hp
    subst hp
    have hMp := leader_parent_mnotarised_all (r := j) (T := Nat.find hreach + 2 * Δ)
      hinit hh hs R (le_refl _)
    exact ancestors_delivered hinit hh hb hs hMp (by omega) (by omega) a hap

end Minimmit
