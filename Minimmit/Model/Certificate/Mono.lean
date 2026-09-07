import Minimmit.Model.Certificate.Basic

/-!
# 証明書の補題

S 上の述語は S について単調。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

theorem voters_subset {S S' : Finset (Msg n Tx)} (h : S ⊆ S') (b : Block n Tx) :
    voters S b ⊆ voters S' b := fun q hq => by
  simp only [voters, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  exact h hq

theorem nullifiers_subset {S S' : Finset (Msg n Tx)} (h : S ⊆ S') (v : View) :
    nullifiers S v ⊆ nullifiers S' v := fun q hq => by
  simp only [nullifiers, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  exact h hq

theorem MNotarised.mono {f : Nat} {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {b : Block n Tx}
    (hb : MNotarised f S b) : MNotarised f S' b :=
  hb.trans (Finset.card_le_card (voters_subset h b))

theorem LNotarised.mono {f : Nat} {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {b : Block n Tx}
    (hb : LNotarised f S b) : LNotarised f S' b :=
  hb.trans (Finset.card_le_card (voters_subset h b))

theorem Nullified.mono {f : Nat} {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {v : View}
    (hv : Nullified f S v) : Nullified f S' v :=
  hv.trans (Finset.card_le_card (nullifiers_subset h v))

omit [DecidableEq Tx] in
theorem NoProgressWitness.mono {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {v : View}
    {x : Option (Block n Tx)} {q : Fin n} (hq : NoProgressWitness S v x q) :
    NoProgressWitness S' v x q := by
  cases hq with
  | nullify hm => exact .nullify (h hm)
  | vote b hv hne hm => exact .vote b hv hne (h hm)

omit [DecidableEq Tx] in
theorem noProgressWitnesses_subset {S S' : Finset (Msg n Tx)} (h : S ⊆ S') (v : View)
    (x : Option (Block n Tx)) : noProgressWitnesses S v x ⊆ noProgressWitnesses S' v x :=
  fun q hq => by
    simp only [noProgressWitnesses, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact hq.mono h

omit [DecidableEq Tx] in
theorem NoProgress.mono {f : Nat} {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {v : View}
    {x : Option (Block n Tx)} (hx : NoProgress f S v x) : NoProgress f S' v x :=
  hx.trans (Finset.card_le_card (noProgressWitnesses_subset h v x))

omit [DecidableEq Tx] in
theorem mem_noProgressWitnesses {S : Finset (Msg n Tx)} {v : View} {x : Option (Block n Tx)}
    {q : Fin n} : q ∈ noProgressWitnesses S v x ↔ NoProgressWitness S v x q := by
  simp [noProgressWitnesses]

theorem mem_voters {S : Finset (Msg n Tx)} {b : Block n Tx} {q : Fin n} :
    q ∈ voters S b ↔ Msg.vote q b ∈ S := by
  simp [voters]

theorem mem_nullifiers {S : Finset (Msg n Tx)} {v : View} {q : Fin n} :
    q ∈ nullifiers S v ↔ Msg.nullify q v ∈ S := by
  simp [nullifiers]

/-! ### View と Block -/

theorem View.val_injective {a b : View} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

omit [DecidableEq Tx] in
theorem Block.Ancestor.trans {a b c : Block n Tx} (hab : Block.Ancestor a b)
    (hbc : Block.Ancestor b c) : Block.Ancestor a c := by
  induction hbc with
  | refl => exact hab
  | parent q v tr p _ ih => exact Block.Ancestor.parent q v tr p ih

omit [DecidableEq Tx] in
/-- view が 1 以上のブロックは genesis でない。 -/
theorem Block.ne_gen_of_one_le {b : Block n Tx} (h : 1 ≤ b.view.val) : b ≠ .gen := by
  intro hg; subst hg; simp [Block.view] at h

omit [DecidableEq Tx] in
/-- view が 1 以上のブロックへの票は、genesis への票でない。 -/
theorem Msg.vote_ne_gen_vote {q : Fin n} {b : Block n Tx} (h : 1 ≤ b.view.val) :
    Msg.vote q b ≠ Msg.vote q .gen := by
  intro h'; injection h' with _ hb; subst hb; simp [Block.view] at h

omit [DecidableEq Tx] in
/-- genesis はすべてのブロックの祖先。 -/
theorem Block.gen_ancestor (b : Block n Tx) : Block.Ancestor Block.gen b := by
  induction b with
  | gen => exact Block.Ancestor.refl _
  | node q v tr p ih => exact Block.Ancestor.parent q v tr p ih

omit [DecidableEq Tx] in
/-- view が v₁ 以上のブロックの祖先の鎖には、view が v₁ 以上で親の view が v₁ 未満の
    ブロックがある。 -/
theorem Block.exists_crossing {b : Block n Tx} {v₁ : Nat} (h1 : 1 ≤ v₁) (hb : v₁ ≤ b.view.val) :
    ∃ q v tr p, Block.Ancestor (Block.node q v tr p) b ∧ v₁ ≤ v.val ∧ p.view.val < v₁ := by
  induction b with
  | gen => simp [Block.view] at hb; omega
  | node q v tr p ih =>
    by_cases hp : p.view.val < v₁
    · exact ⟨q, v, tr, p, Block.Ancestor.refl _, hb, hp⟩
    · obtain ⟨q', v', tr', p', ha, h1', h2'⟩ := ih (not_lt.mp hp)
      exact ⟨q', v', tr', p', Block.Ancestor.parent q v tr p ha, h1', h2'⟩

end Minimmit
