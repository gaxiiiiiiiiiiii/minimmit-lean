import Minimmit.Analysis.Liveness.Lemma5_7

/-!
# log と §2 の性質

論文の log_i は finalise が書く変数で、その値は S から定まる: finalise したブロックのうち
最も深いものの Tr*。ここでは log を S の関数として定義し、§2 の Consistency と Liveness を
論文の文どおりに定義して、ブロックの形の Lemma 5.4・5.7 から導く。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ : Nat} {GST : Time} {lead : View → Fin n} {s₀ : State n Tx}
  {instrs : Nat → Instr n Tx}

open Classical in
/-- S で finalise したブロックの列 -/
noncomputable def finalisedBlocks (f : Nat) (S : Finset (Msg n Tx)) : List (Block n Tx) :=
  (Algo.votedBlocks S).filter fun b => decide (Finalised f S b)

/-- p_i の log（§2）: finalise したブロックのうち最も深いものの Tr*。無ければ空。 -/
noncomputable def log (f : Nat) (S : Finset (Msg n Tx)) : List Tx :=
  match (finalisedBlocks f S).argmax Block.depth with
  | some b => b.trStar
  | none => []

/-- Consistency（§2）: 正直な p_i・p_j の log_i(t) と log_j(t′) は、一方が他方の接頭辞。 -/
def Consistency (f : Nat) (s₀ : State n Tx) (instrs : Nat → Instr n Tx) : Prop :=
  ∀ i j, Correct s₀ instrs i → Correct s₀ instrs j → ∀ t t',
    log f ((State.run s₀ instrs t).procs i).S <+: log f ((State.run s₀ instrs t').procs j).S
    ∨ log f ((State.run s₀ instrs t').procs j).S <+: log f ((State.run s₀ instrs t).procs i).S

/-- Liveness（§2）: 正直な p_i が受け取った取引は、正直な p_j の log にいずれ入る。 -/
def Liveness (f : Nat) (s₀ : State n Tx) (instrs : Nat → Instr n Tx) : Prop :=
  ∀ i j, Correct s₀ instrs i → Correct s₀ instrs j → ∀ t (tr : Tx),
    Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S →
    ∃ t', tr ∈ log f ((State.run s₀ instrs t').procs j).S

theorem mem_finalisedBlocks {S : Finset (Msg n Tx)} {b : Block n Tx} :
    b ∈ finalisedBlocks f S ↔ b ∈ Algo.votedBlocks S ∧ Finalised f S b := by
  simp [finalisedBlocks]

/-- finalise したブロックが祖先関係で鎖をなすなら、log はそのどれよりも深い finalise した
    ブロックの Tr*。 -/
theorem log_eq_of_finalised {S : Finset (Msg n Tx)}
    (hchain : ∀ b b', Finalised f S b → Finalised f S b' →
      Block.Ancestor b b' ∨ Block.Ancestor b' b)
    {b : Block n Tx} (hb : Finalised f S b) (hvb : b ∈ Algo.votedBlocks S) :
    ∃ b', Finalised f S b' ∧ Block.Ancestor b b' ∧ log f S = b'.trStar := by
  have hmem : b ∈ finalisedBlocks f S := mem_finalisedBlocks.mpr ⟨hvb, hb⟩
  unfold log
  cases hl : (finalisedBlocks f S).argmax Block.depth with
  | none => exact absurd (List.argmax_eq_none.mp hl ▸ hmem) (List.not_mem_nil)
  | some b' =>
    have hb' := (mem_finalisedBlocks.mp (List.argmax_mem (Option.mem_def.mpr hl))).2
    have hle : b.depth ≤ b'.depth := List.le_of_mem_argmax hmem (Option.mem_def.mpr hl)
    refine ⟨b', hb', ?_, rfl⟩
    rcases hchain b b' hb hb' with h | h
    · exact h
    · rw [Block.eq_of_ancestor_of_depth_le h hle]; exact Block.Ancestor.refl _

/-- Lemma 5.4（Consistency）: プロトコルは Consistency を満たす。 -/
theorem satisfies_consistency (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hbz : ByzBound f s₀ instrs) : Consistency f s₀ instrs := by
  intro i j _ _ t t'
  unfold log
  cases hl : (finalisedBlocks f ((State.run s₀ instrs t).procs i).S).argmax Block.depth with
  | none => exact Or.inl (List.nil_prefix)
  | some b =>
    cases hl' : (finalisedBlocks f ((State.run s₀ instrs t').procs j).S).argmax Block.depth with
    | none => exact Or.inr (List.nil_prefix)
    | some b' =>
      have hb := (mem_finalisedBlocks.mp (List.argmax_mem (Option.mem_def.mpr hl))).2
      have hb' := (mem_finalisedBlocks.mp (List.argmax_mem (Option.mem_def.mpr hl'))).2
      rcases consistency hn hinit hh hbz hb.1 hb'.1 with h | h
      · exact Or.inl (Block.trStar_prefix_of_ancestor h)
      · exact Or.inr (Block.trStar_prefix_of_ancestor h)

/-- Lemma 5.7（Liveness）: プロトコルは Liveness を満たす。 -/
theorem satisfies_liveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hbz : ByzBound f s₀ instrs)
    (hs : PartialSync Δ GST s₀ instrs) (hlead : Fair lead) : Liveness f s₀ instrs := by
  intro i j hi _ t tr htr
  obtain ⟨t', b, hfin, hmem⟩ := liveness (j := j) hn hinit hh hbz hs hlead hi htr
  have hvb : b ∈ Algo.votedBlocks ((State.run s₀ instrs t').procs j).S := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega) (show n - f ≤ _ from hfin.1))
    exact Algo.mem_votedBlocks (mem_voters.mp hw)
  obtain ⟨b', _, hanc, hlog⟩ := log_eq_of_finalised
    (fun x y hx hy => consistency hn hinit hh hbz hx.1 hy.1) hfin hvb
  refine ⟨t', ?_⟩
  rw [hlog]
  exact (Block.trStar_prefix_of_ancestor hanc).subset hmem

end Minimmit
