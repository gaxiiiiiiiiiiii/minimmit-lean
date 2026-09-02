import Minimmit.Model.Transition
import Mathlib.Data.Fintype.Basic

/-!
# 証明書

§4 の用語（M/L-notarisation・nullification・valid proposal・進捗のなさの証拠）を
message の集合 S 上の述語として定義し、§5.1 の「b が M-notarisation を受ける」などを
実行上の述語として定義する。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type}

section
variable [DecidableEq Tx]

/-! ### notarisation と nullification -/

/-- b への票を S に持つ署名者。 -/
def voters (S : Finset (Msg n Tx)) (b : Block Tx) : Finset (Fin n) :=
  Finset.univ.filter fun q => Msg.vote q b ∈ S

/-- nullify(v) を S に持つ署名者。 -/
def nullifiers (S : Finset (Msg n Tx)) (v : View) : Finset (Fin n) :=
  Finset.univ.filter fun q => Msg.nullify q v ∈ S

/-- S が b の M-notarisation を含む（§4）: 異なる 2f + 1 人の票。genesis は常に含む
    （§5.1 の規約）。 -/
def MNotarised (f : Nat) (S : Finset (Msg n Tx)) (b : Block Tx) : Prop :=
  b = .gen ∨ 2 * f + 1 ≤ (voters S b).card

instance (f : Nat) (S : Finset (Msg n Tx)) (b : Block Tx) : Decidable (MNotarised f S b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- S が b の L-notarisation を含む（§4）: 異なる n − f 人の票。genesis は常に含む
    （§5.1 の規約）。 -/
def LNotarised (f : Nat) (S : Finset (Msg n Tx)) (b : Block Tx) : Prop :=
  b = .gen ∨ n - f ≤ (voters S b).card

instance (f : Nat) (S : Finset (Msg n Tx)) (b : Block Tx) : Decidable (LNotarised f S b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- S が view v の nullification を含む（§4）: 異なる 2f + 1 人の nullify(v)。 -/
def Nullified (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Prop :=
  2 * f + 1 ≤ (nullifiers S v).card

instance (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Decidable (Nullified f S v) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ### valid proposal -/

/-- S が view v の valid proposal b を含む（§4）。 -/
structure ValidProposal (f : Nat) (lead : View → Fin n) (S : Finset (Msg n Tx)) (v : View)
    (b : Block Tx) : Prop where
  /-- (i) b は view v のブロック。 -/
  view : b.view = v
  /-- (i) b は lead(v) の署名付きで S にある。 -/
  signed : Msg.block (lead v) b ∈ S
  /-- (i) lead(v) の署名付きの view v のブロックは S に b しかない。 -/
  unique : ∀ b', b'.view = v → Msg.block (lead v) b' ∈ S → b' = b
  /-- b は genesis でなく、親を持つ。 -/
  ne_gen : b ≠ .gen
  /-- (ii) 親の M-notarisation。 -/
  parent : ∀ p ∈ b.parent, MNotarised f S p
  /-- (iii) 親の view と v の間の各 view の nullification。 -/
  gaps : ∀ p ∈ b.parent, ∀ w : View, p.view.val < w.val → w.val < v.val → Nullified f S w

/-! ### 進捗のなさの証拠 -/

/-- q が view v の進捗のなさを証言する（Algorithm 1 の 24〜27 行）: nullify(v) を
    送ったか、notarised 以外の view v のブロックに投票した。 -/
inductive Dissents (S : Finset (Msg n Tx)) (v : View) (notarised : Option (Block Tx))
    (q : Fin n) : Prop where
  /-- (i) nullify(v) が S にある。 -/
  | nullify (h : Msg.nullify q v ∈ S) : Dissents S v notarised q
  /-- (ii) notarised 以外の view v のブロック b への票が S にある。 -/
  | vote (b : Block Tx) (hv : b.view = v) (hne : some b ≠ notarised)
      (h : Msg.vote q b ∈ S) : Dissents S v notarised q

open Classical in
/-- view v の進捗のなさを証言する署名者。 -/
noncomputable def dissenters (S : Finset (Msg n Tx)) (v : View)
    (notarised : Option (Block Tx)) : Finset (Fin n) :=
  Finset.univ.filter (Dissents S v notarised)

/-- view v で進捗がない証拠（Algorithm 1 の 24〜27 行）: 証言する署名者が 2f + 1 人以上。 -/
def NoProgress (f : Nat) (S : Finset (Msg n Tx)) (v : View)
    (notarised : Option (Block Tx)) : Prop :=
  2 * f + 1 ≤ (dissenters S v notarised).card

end

/-! ### 実行上の証明書（§5.1）
誰かの S でなく、実行の中で誰が何を送ったかで言う。 -/

open Classical in
/-- b への自分の票を送ったプロセッサ。 -/
noncomputable def voteSenders (instrs : Nat → Instr n Tx) (b : Block Tx) : Finset (Fin n) :=
  Finset.univ.filter fun q => Sends instrs q (.vote q b)

open Classical in
/-- nullify(v) を送ったプロセッサ。 -/
noncomputable def nullifySenders (instrs : Nat → Instr n Tx) (v : View) : Finset (Fin n) :=
  Finset.univ.filter fun q => Sends instrs q (.nullify q v)

/-- b が M-notarisation を受ける（§5.1）: b = genesis か、2f + 1 人以上が b に投票した。 -/
def ReceivesM (f : Nat) (instrs : Nat → Instr n Tx) (b : Block Tx) : Prop :=
  b = .gen ∨ 2 * f + 1 ≤ (voteSenders instrs b).card

/-- b が L-notarisation を受ける（§5.1）: b = genesis か、n − f 人以上が b に投票した。 -/
def ReceivesL (f : Nat) (instrs : Nat → Instr n Tx) (b : Block Tx) : Prop :=
  b = .gen ∨ n - f ≤ (voteSenders instrs b).card

/-- view v が nullification を受ける（§5.1）: 2f + 1 人以上が nullify(v) を送った。 -/
def ReceivesNullification (f : Nat) (instrs : Nat → Instr n Tx) (v : View) : Prop :=
  2 * f + 1 ≤ (nullifySenders instrs v).card

end Minimmit
