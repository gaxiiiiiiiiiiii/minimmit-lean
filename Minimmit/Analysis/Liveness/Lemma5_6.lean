import Minimmit.Analysis.Liveness.LeaderRound

/-!
# Lemma 5.6（Correct leaders finalise blocks）
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-- Lemma 5.6（Correct leaders finalise blocks）: lead(v) が正直で、最初の正直者が GST 以降に
    view v に入るなら、lead(v) はあるスロットに view v のブロックを全員へ送り、それは
    L-notarisation を受ける。 -/
theorem correct_leader_finalises (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hs : PartialSync Δ s₀ instrs) {v : View} (hv : 1 ≤ v.val) (hi : Correct s₀ instrs (lead v))
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : hs.GST.val ≤ t) :
    ∃ b : Block Tx, b.view = v
      ∧ (∃ t', ∀ j, Action.send (.block (lead v) b) j ∈ (instrs t').actions (lead v))
      ∧ ReceivesL f instrs b := by
  obtain ⟨e, R⟩ := leader_round hinit hh hs (le_refl Δ) hv hi hfirst hgst
  refine ⟨leaderBlockAt f lead s₀ instrs v e, leaderBlockAt_view hinit hh hb hs R,
    ⟨e, fun j => leader_proposes hinit hh hb hs R j⟩, ?_⟩
  right
  refine (card_correctSet hb).trans (Finset.card_le_card fun r hr => ?_)
  exact mem_voteSenders.mpr (all_vote_leaderBlock hinit hh hb hs R hn (mem_correctSet.mp hr))

end Minimmit
