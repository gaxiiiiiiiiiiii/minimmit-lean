import Minimmit.Model.Certificate.Mono
import Minimmit.Model.Constraint.Basic

/-!
# log と §2 の性質

log を S の関数として定義し、§2 の compatible・Consistency・Liveness を定義する。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f : Nat} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

open Classical in
/-- 投票されたブロックのうち `Finalised` なものの列 -/
noncomputable def finalisedBlocks (f : Nat) (S : Finset (Msg n Tx)) : List (Block n Tx) :=
  (Algo.votedBlocks S).filter fun b => decide (Finalised f S b)

/-- p_i の log（§2）: finalise したブロックのうち最も深いものの Tr*。無ければ空。 -/
noncomputable def log (f : Nat) (S : Finset (Msg n Tx)) : List Tx :=
  match (finalisedBlocks f S).argmax Block.depth with
  | some b => b.trStar
  | none => []

/-- compatible（§2）: 一方が他方の接頭辞。 -/
def Compatible (σ τ : List Tx) : Prop := σ <+: τ ∨ τ <+: σ

/-- Consistency（§2）: 正直な p_i・p_j の log_i(t) と log_j(t′) は compatible。 -/
def Consistency (f : Nat) (s₀ : State n Tx) (instrs : Nat → Instr n Tx) : Prop :=
  ∀ i j, Correct s₀ instrs i → Correct s₀ instrs j → ∀ t t',
    Compatible (log f ((State.stateAt s₀ instrs t).procs i).S)
      (log f ((State.stateAt s₀ instrs t').procs j).S)

/-- Liveness（§2）: 正直な p_i が受け取った取引は、正直な p_j の log にいずれ入る。 -/
def Liveness (f : Nat) (s₀ : State n Tx) (instrs : Nat → Instr n Tx) : Prop :=
  ∀ i j, Correct s₀ instrs i → Correct s₀ instrs j → ∀ t (tr : Tx),
    Msg.tx tr ∈ ((State.stateAt s₀ instrs t).procs i).S →
    ∃ t', tr ∈ log f ((State.stateAt s₀ instrs t').procs j).S

theorem mem_finalisedBlocks {S : Finset (Msg n Tx)} {b : Block n Tx} :
    b ∈ finalisedBlocks f S ↔ b ∈ Algo.votedBlocks S ∧ Finalised f S b := by
  simp [finalisedBlocks]

/-- finalise したブロックのどの 2 つも一方が他方の祖先なら、投票された finalise したブロック b
    について、b を祖先に持つ finalise したブロック b′ があり、log は b′ の Tr*。 -/
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

/-- S ⊆ S′ で、S′ で finalise したブロックのどの 2 つも一方が他方の祖先なら、S の log は S′ の
    log の接頭辞。 -/
theorem log_prefix_of_subset {S S' : Finset (Msg n Tx)} (hS : S ⊆ S')
    (hchain : ∀ b b', Finalised f S' b → Finalised f S' b' →
      Block.Ancestor b b' ∨ Block.Ancestor b' b) :
    log f S <+: log f S' := by
  unfold log
  cases hl : (finalisedBlocks f S).argmax Block.depth with
  | none => exact List.nil_prefix
  | some b =>
    obtain ⟨hvb, hb⟩ := mem_finalisedBlocks.mp (List.argmax_mem (Option.mem_def.mpr hl))
    obtain ⟨b', -, hanc, hlog⟩ :=
      log_eq_of_finalised hchain (hb.mono hS) (Algo.mem_votedBlocks_of_subset hS hvb)
    unfold log at hlog
    rw [hlog]
    exact Block.trStar_prefix_of_ancestor hanc

end Minimmit
