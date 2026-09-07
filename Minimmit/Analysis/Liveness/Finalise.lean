import Minimmit.Analysis.Consistency.Lemma5_4
import Minimmit.Analysis.Liveness.Timing

/-!
# 確定と祖先の到着

論文の finalise は、S に b の L-notarisation があり、b の全祖先を S が含むときに log を
b.Tr* に伸ばす（§2、Algorithm 1 の 31〜32 行）。`Finalised` がその条件。b の L-notarisation の
票は b を成分に持つが祖先は持たないので、祖先が S に入ることは別に示す。論文の Lemma 5.7・5.10
の証明が「各祖先は M-notarisation を受けているので f + 1 人の正直者がその票を全員へ送って
いる」と論じる部分に当たる。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {GST : Time} {lead : View → Fin n} {s₀ : State n Tx}
  {instrs : Nat → Instr n Tx}

theorem Finalised.mono {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {b : Block n Tx}
    (hb : Finalised f S b) : Finalised f S' b :=
  ⟨hb.1.mono h, fun a ha => containsBlock_mono h (hb.2 a ha)⟩

omit [DecidableEq Tx] in
/-- 祖先は、自分自身か、親の祖先。 -/
theorem Block.Ancestor.eq_or_parent {a b : Block n Tx} (h : Block.Ancestor a b) :
    a = b ∨ ∃ p ∈ b.parent, Block.Ancestor a p := by
  cases h with
  | refl => exact Or.inl rfl
  | parent q v tr p hp => exact Or.inr ⟨p, rfl, hp⟩

/-- スロット s の誰かの S に M-notarised なブロックの、genesis でない各祖先には、s より前に
    それへの票を送った正直者がいる。b の最初の正直な票は valid proposal によるので、その
    正直者の S に親の M-notarisation があり、親についても同じことが言える。 -/
theorem ancestor_vote_before (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) :
    ∀ (b : Block n Tx) {i : Fin n} {s : Nat},
      MNotarised f ((State.run s₀ instrs s).procs i).S b →
      ∀ a, Block.Ancestor a b → a ≠ .gen →
        ∃ w s', Correct s₀ instrs w ∧ s' < s
          ∧ ∃ j, Action.send (Msg.vote w a) j ∈ (instrs s').actions w
  | .gen, _, _, _, _, ha, hg => by
    cases ha; exact absurd rfl hg
  | .node q v tr p, i, s, hM, a, ha, hg => by
    obtain ⟨w, hw, hwc⟩ := exists_correct_of_lt_card hb
      (lt_of_lt_of_le (by omega) (show 2 * f + 1 ≤ _ from hM))
    rw [mem_voters] at hw
    obtain ⟨s', hs', j, hj⟩ := sendsBefore_of_mem_S hinit hw rfl (by simp)
    rcases ha.eq_or_parent with rfl | ⟨p', hp', hap⟩
    · exact ⟨w, s', hwc, hs', j, hj⟩
    · simp only [Block.parent, Option.mem_def, Option.some.injEq] at hp'
      subst hp'
      have hRM : ReceivesM f instrs (.node q v tr p) := receivesM_of_MNotarised hinit hM
      obtain ⟨q', t₀, hq'c, _, hvp, hmin⟩ := exists_valid_proposal_vote hinit hh hb (by simp) hRM
      have ht₀ : t₀ ≤ s' := hmin s' w j hwc hj
      have hMp : MNotarised f ((State.run s₀ instrs (t₀ + 1)).procs q').S p :=
        (hvp.parent p (by simp [Block.parent])).mono
          ((Algo.S_st2_subset_st5 f Δ lead q' _).trans (S_st5_subset_succ hh hq'c t₀))
      obtain ⟨w', s'', hw'c, hs'', hsend⟩ := ancestor_vote_before hinit hh hb p hMp a hap hg
      exact ⟨w', s'', hw'c, by omega, hsend⟩

/-- 祖先の到着: スロット s の誰かの S に M-notarised なブロックの全祖先は、max(GST, s) + δ
    までに全員の S に含まれる。 -/
theorem ancestors_delivered (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) (hs : PartialSync δ GST s₀ instrs)
    {i : Fin n} {s : Nat} {b : Block n Tx} (hM : MNotarised f ((State.run s₀ instrs s).procs i).S b)
    {j : Fin n} {T : Nat} (hT₁ : s ≤ T) (hT₂ : max GST.val s + δ ≤ T) :
    ∀ a, Block.Ancestor a b → containsBlock ((State.run s₀ instrs T).procs j).S a := by
  intro a ha
  by_cases hg : a = .gen
  · subst hg
    exact ⟨.vote j .gen, genesisS_subset_run hinit j T (mem_genesisS.mpr ⟨j, rfl⟩), rfl⟩
  obtain ⟨w, s', hwc, hs', j', hj'⟩ := ancestor_vote_before hinit hh hb b hM a ha hg
  have hsend : Action.send (Msg.vote w a) j ∈ (instrs s').actions w := by
    rw [hh s' w (hwc s')] at hj' ⊢
    exact Algo.send_all hj' j
  refine ⟨Msg.vote w a, ?_, rfl⟩
  exact delivered hinit hh hs hwc hsend (by omega)
    (le_trans (Nat.add_le_add_right (max_le_max (le_refl _) hs'.le) δ) hT₂)

end Minimmit
