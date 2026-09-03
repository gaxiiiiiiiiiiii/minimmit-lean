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
structure Init (s₀ : State n Tx) : Prop where
  procs : ∀ i, s₀.procs i = Processor.init
  byz : s₀.byz = ∅
  pool : s₀.pool = ∅
  now : s₀.now = ⟨0⟩

/-! ### 部分同期 -/

/-- 状態 s で、期限 max(GST, sentAt) + Δ に達した packet は宛先の S に入っている。 -/
def State.Timely (Δ : Nat) (GST : Time) (s : State n Tx) : Prop :=
  ∀ x ∈ s.pool, max GST.val x.sentAt.val + Δ ≤ s.now.val → x.msg ∈ (s.procs x.dst).S

/-- 部分同期（§2）: ある GST があって、t に送られた packet は max(GST, t) + Δ までに
    宛先の S に入る。Δ は既知、GST は敵が選ぶ。Δ ≥ 1 は、論文の「t に送った message は
    t′ > t に届く」から従う条件で、`Timely` がスロット境界でしか判定しないため明示する。 -/
structure PartialSync [DecidableEq Tx] (Δ : Nat) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) where
  GST : Time
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

/-! ### プロトコルに従うこと -/

/-- 腐敗していないプロセッサは Algorithm 1 に従う: 全スロット t で、`(run t).byz` にない i
    の動作は `Algo.step` の出力。 -/
def Honest [DecidableEq Tx] (f Δ : Nat) (lead : View → Fin n) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) : Prop :=
  ∀ t i, i ∉ (State.run s₀ instrs t).byz →
    (instrs t).actions i = Algo.step f Δ lead i ((State.run s₀ instrs t).procs i)

end Minimmit
