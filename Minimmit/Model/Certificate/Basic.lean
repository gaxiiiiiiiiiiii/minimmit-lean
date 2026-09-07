import Minimmit.Model.Transition.Basic
import Mathlib.Data.Fintype.Basic

/-!
# 証明書

§4 の用語（M/L-notarisation・nullification・valid proposal・proof of no progress）を
message の集合 S 上の述語として定義し、§5.1 の「b が M-notarisation を受ける」などを
実行上の述語として定義する。

## 論文からの差異

- 初期状態の S は空で、Table 2 が初期の S に含める genesis の M/L-notarisation は、
  `MNotarised`・`LNotarised` が genesis を無条件に認めることで表す。S 上の述語の値は、
  初期 S に genesis の notarisation を含めた場合と同じ。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type}

section
variable [DecidableEq Tx]

/-! ### notarisation と nullification -/

/-- b への票を S に持つ署名者 -/
def voters (S : Finset (Msg n Tx)) (b : Block n Tx) : Finset (Fin n) :=
  Finset.univ.filter fun q => Msg.vote q b ∈ S

/-- nullify(v) を S に持つ署名者 -/
def nullifiers (S : Finset (Msg n Tx)) (v : View) : Finset (Fin n) :=
  Finset.univ.filter fun q => Msg.nullify q v ∈ S

/-- S が b の M-notarisation を含む（§4）: 異なる 2f + 1 人の票。genesis は常に含む。 -/
def MNotarised (f : Nat) (S : Finset (Msg n Tx)) (b : Block n Tx) : Prop :=
  b = .gen ∨ 2 * f + 1 ≤ (voters S b).card

instance (f : Nat) (S : Finset (Msg n Tx)) (b : Block n Tx) : Decidable (MNotarised f S b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- S が b の L-notarisation を含む（§4）: 異なる n − f 人の票。genesis は常に含む。 -/
def LNotarised (f : Nat) (S : Finset (Msg n Tx)) (b : Block n Tx) : Prop :=
  b = .gen ∨ n - f ≤ (voters S b).card

instance (f : Nat) (S : Finset (Msg n Tx)) (b : Block n Tx) : Decidable (LNotarised f S b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- S が view v の nullification を含む（§4）: 異なる 2f + 1 人の nullify(v)。 -/
def Nullified (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Prop :=
  2 * f + 1 ≤ (nullifiers S v).card

instance (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Decidable (Nullified f S v) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ### valid proposal -/

/-- S が view v の valid proposal b を含む（§4）。 -/
structure ValidProposal (f : Nat) (lead : View → Fin n) (S : Finset (Msg n Tx)) (v : View)
    (b : Block n Tx) : Prop where
  /-- (i) b は view v のブロック。 -/
  view : b.view = v
  /-- (i) b は lead(v) の署名付き。 -/
  signed : b.signer = some (lead v)
  /-- (i) S は b を含む。 -/
  mem : containsBlock S b
  /-- (i) lead(v) の署名付きの view v のブロックで S が含むのは b だけ。 -/
  unique : ∀ b', b'.view = v → b'.signer = some (lead v) → containsBlock S b' → b' = b
  /-- b は genesis でなく、親を持つ。 -/
  ne_gen : b ≠ .gen
  /-- (ii) 親の M-notarisation -/
  parent : ∀ p ∈ b.parent, MNotarised f S p
  /-- (iii) 親の view と v の間の各 view の nullification -/
  gaps : ∀ p ∈ b.parent, ∀ w : View, p.view.val < w.val → w.val < v.val → Nullified f S w

/-! ### proof of no progress -/

/-- q が view v の proof of no progress に寄与する（Algorithm 1 の 24〜27 行）: nullify(v)
    を送ったか、notarised 以外の view v のブロックに投票した。論文はこの条件に名前を
    付けておらず、29 行の注釈 "proof of no progress" から名付けた。 -/
inductive NoProgressWitness (S : Finset (Msg n Tx)) (v : View) (notarised : Option (Block n Tx))
    (q : Fin n) : Prop where
  /-- (i) nullify(v) が S にある。 -/
  | nullify (h : Msg.nullify q v ∈ S) : NoProgressWitness S v notarised q
  /-- (ii) notarised 以外の view v のブロック b への票が S にある。 -/
  | vote (b : Block n Tx) (hv : b.view = v) (hne : some b ≠ notarised)
      (h : Msg.vote q b ∈ S) : NoProgressWitness S v notarised q

open Classical in
/-- view v の proof of no progress に寄与する署名者 -/
noncomputable def noProgressWitnesses (S : Finset (Msg n Tx)) (v : View)
    (notarised : Option (Block n Tx)) : Finset (Fin n) :=
  Finset.univ.filter (NoProgressWitness S v notarised)

/-- view v の proof of no progress が S にある（Algorithm 1 の 24〜27 行）: 寄与する署名者が
    2f + 1 人以上。 -/
def NoProgress (f : Nat) (S : Finset (Msg n Tx)) (v : View)
    (notarised : Option (Block n Tx)) : Prop :=
  2 * f + 1 ≤ (noProgressWitnesses S v notarised).card

end

/-! ### 実行上の証明書（§5.1）
誰かの S でなく、実行の中で誰が何を送ったかで言う。 -/

open Classical in
/-- b への自分の票を送ったプロセッサ -/
noncomputable def voteSenders (instrs : Nat → Instr n Tx) (b : Block n Tx) : Finset (Fin n) :=
  Finset.univ.filter fun q => Sends instrs q (.vote q b)

open Classical in
/-- nullify(v) を送ったプロセッサ -/
noncomputable def nullifySenders (instrs : Nat → Instr n Tx) (v : View) : Finset (Fin n) :=
  Finset.univ.filter fun q => Sends instrs q (.nullify q v)

/-- b が M-notarisation を受ける（§5.1）: b = genesis か、2f + 1 人以上が b に投票した。 -/
def ReceivesM (f : Nat) (instrs : Nat → Instr n Tx) (b : Block n Tx) : Prop :=
  b = .gen ∨ 2 * f + 1 ≤ (voteSenders instrs b).card

/-- b が L-notarisation を受ける（§5.1）: b = genesis か、n − f 人以上が b に投票した。 -/
def ReceivesL (f : Nat) (instrs : Nat → Instr n Tx) (b : Block n Tx) : Prop :=
  b = .gen ∨ n - f ≤ (voteSenders instrs b).card

/-- view v が nullification を受ける（§5.1）: 2f + 1 人以上が nullify(v) を送った。 -/
def ReceivesNullification (f : Nat) (instrs : Nat → Instr n Tx) (v : View) : Prop :=
  2 * f + 1 ≤ (nullifySenders instrs v).card

end Minimmit
