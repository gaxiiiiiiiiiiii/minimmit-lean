import Minimmit.Analysis.Liveness.LeaderRound

/-!
# Lemma 5.7（Liveness）

## 論文からの差異

- `liveness` は p_j の正直さを仮定しない。論文は正直者 p_j について述べるが、`PartialSync` は
  腐敗したプロセッサ宛の配送も保証するので要らない。論文の主張を含む。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {GST : Time} {lead : View → Fin n} {s₀ : State n Tx}
  {instrs : Nat → Instr n Tx}

/-- Lemma 5.7（Liveness）: 正直者 p_i が受け取った取引は、あるスロットで任意の p_j が
    L-notarisation を持つブロックの Tr* に入る。 -/
theorem liveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hs : PartialSync Δ GST s₀ instrs) (hlead : Fair lead)
    {i j : Fin n} (hi : Correct s₀ instrs i)
    {t : Nat} {tr : Tx} (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S) :
    ∃ t' b, LNotarised f ((State.run s₀ instrs t').procs j).S b ∧ tr ∈ b.trStar := by
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
    obtain ⟨s, hs'⟩ := progression hn hinit hh hb hs hi v'
    exact ⟨s, i, hi, hs'.trans (viewAt_le_succ i s)⟩
  have hfirst : FirstEntry s₀ instrs v' (Nat.find hreach) :=
    ⟨Nat.find_spec hreach, fun r t' hr h => Nat.find_min' hreach ⟨r, hr, h⟩⟩
  have hgst : max GST.val t < Nat.find hreach := by
    obtain ⟨r, hr, h⟩ := Nat.find_spec hreach
    by_contra hle
    have h1 := viewAt_mono (s₀ := s₀) (instrs := instrs) r (Nat.add_le_add_right (not_lt.mp hle) 1)
    have h2 := hbound r
    omega
  have hlc : Correct s₀ instrs (lead v') := hlv' ▸ hi
  obtain ⟨e, R⟩ := leader_round hinit hh hs (le_refl Δ) hv'1 hlc hfirst (by omega)
  have hte := first_entry_le_leader_entry R
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
  refine ⟨T + GST.val + Δ + 1, leaderBlockAt f lead s₀ instrs v' e, ?_, htr'⟩
  right
  refine (card_correctSet hb).trans (Finset.card_le_card fun r hr => ?_)
  obtain ⟨s, hsT, j', hj'⟩ := hT r hr
  have hrc := mem_correctSet.mp hr
  have hj'' : Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v' e)) j
      ∈ (instrs s).actions r := by
    rw [hh s r (hrc s)] at hj' ⊢
    exact Algo.send_all hj' j
  rw [mem_voters]
  exact delivered hinit hh hs hrc hj'' (by omega) (by omega)

end Minimmit
