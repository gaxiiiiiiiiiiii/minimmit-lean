import Minimmit.Model.Algo.Basic

/-!
# 制約

遷移系が課さない規則。定理の仮定になる。初期状態、部分同期、腐敗、リーダー、
プロトコルに従うこと、の順。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type}

/-! ### 初期状態 -/

/-- 初期状態: 全プロセッサが `Processor.init`、byz と pool は空、now は 0。 -/
structure Init [DecidableEq Tx] (s₀ : State n Tx) : Prop where
  procs : ∀ i, s₀.procs i = Processor.init
  byz : s₀.byz = ∅
  pool : s₀.pool = ∅
  now : s₀.now = ⟨0⟩

/-! ### 部分同期 -/

/-- 状態 s で、期限 max(GST, sentAt) + Δ に達した packet は宛先の S に入っている。 -/
def State.Timely (Δ : Nat) (GST : Time) (s : State n Tx) : Prop :=
  ∀ x ∈ s.pool, max GST.val x.sentAt.val + Δ ≤ s.now.val → x.msg ∈ (s.procs x.dst).S

/-- 部分同期（§2）: t に送られた packet は max(GST, t) + Δ までに宛先の S に入る。Δ は既知、
    GST は敵が選ぶ。 -/
structure PartialSync [DecidableEq Tx] (Δ : Nat) (GST : Time) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) : Prop where
  timely : ∀ t, (State.run s₀ instrs t).Timely Δ GST
  one_le : 1 ≤ Δ

/-! ### 腐敗 -/

/-- p_i は正直者（§2 の correct）: 全スロットで byz にない。 -/
def Correct [DecidableEq Tx] (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (i : Fin n) :
    Prop :=
  ∀ t, i ∉ (State.run s₀ instrs t).byz

/-- 腐敗するのは最大 f 人（§2）: 全スロットで byz の要素数が f 以下。 -/
def ByzBound [DecidableEq Tx] (f : Nat) (s₀ : State n Tx) (instrs : Nat → Instr n Tx) :
    Prop :=
  ∀ t, (State.run s₀ instrs t).byz.card ≤ f

/-! ### リーダー -/

/-- lead は公平: どのプロセッサも、どの view 以降にも自分がリーダーになる view を持つ。
    論文の lead(v) = p_{(v mod n)+1} はこれを満たす。 -/
def Fair (lead : View → Fin n) : Prop :=
  ∀ i : Fin n, ∀ v : View, ∃ v' : View, v.val ≤ v'.val ∧ lead v' = i

/-- どの fa + 1 個の連続する view にも正直なリーダーがいる（Lemma 5.10 のリーダーの仮定）。
    論文の輪番は、腐敗が fa 人以下ならこれを満たす。 -/
def CorrectLeaderWithin [DecidableEq Tx] (s₀ : State n Tx) (instrs : Nat → Instr n Tx)
    (lead : View → Fin n) (fa : Nat) : Prop :=
  ∀ v : View, ∃ v' : View, v.val ≤ v'.val ∧ v'.val ≤ v.val + fa ∧ Correct s₀ instrs (lead v')

/-! ### プロトコルに従うこと -/

/-- 腐敗していないプロセッサは Algorithm 1 に従う: 全スロット t で、`(run t).byz` にない i
    の動作は `Algo.step` の出力。 -/
def Honest [DecidableEq Tx] (f Δ : Nat) (lead : View → Fin n) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) : Prop :=
  ∀ t i, i ∉ (State.run s₀ instrs t).byz →
    (instrs t).actions i = Algo.step f Δ lead i ((State.run s₀ instrs t).procs i)

end Minimmit
