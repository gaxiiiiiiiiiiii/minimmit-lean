import Minimmit.Model.Certificate

/-!
# 証明書の補題

S 上の述語は S について単調。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

theorem voters_subset {S S' : Finset (Msg n Tx)} (h : S ⊆ S') (b : Block Tx) :
    voters S b ⊆ voters S' b := fun q hq => by
  simp only [voters, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  exact h hq

theorem nullifiers_subset {S S' : Finset (Msg n Tx)} (h : S ⊆ S') (v : View) :
    nullifiers S v ⊆ nullifiers S' v := fun q hq => by
  simp only [nullifiers, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  exact h hq

theorem MNotarised.mono {f : Nat} {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {b : Block Tx}
    (hb : MNotarised f S b) : MNotarised f S' b :=
  hb.imp_right fun hc => hc.trans (Finset.card_le_card (voters_subset h b))

theorem LNotarised.mono {f : Nat} {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {b : Block Tx}
    (hb : LNotarised f S b) : LNotarised f S' b :=
  hb.imp_right fun hc => hc.trans (Finset.card_le_card (voters_subset h b))

theorem Nullified.mono {f : Nat} {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {v : View}
    (hv : Nullified f S v) : Nullified f S' v :=
  hv.trans (Finset.card_le_card (nullifiers_subset h v))

omit [DecidableEq Tx] in
theorem NoProgressWitness.mono {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {v : View}
    {x : Option (Block Tx)} {q : Fin n} (hq : NoProgressWitness S v x q) :
    NoProgressWitness S' v x q := by
  cases hq with
  | nullify hm => exact .nullify (h hm)
  | vote b hv hne hm => exact .vote b hv hne (h hm)

omit [DecidableEq Tx] in
theorem noProgressWitnesses_subset {S S' : Finset (Msg n Tx)} (h : S ⊆ S') (v : View)
    (x : Option (Block Tx)) : noProgressWitnesses S v x ⊆ noProgressWitnesses S' v x :=
  fun q hq => by
    simp only [noProgressWitnesses, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact hq.mono h

omit [DecidableEq Tx] in
theorem NoProgress.mono {f : Nat} {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {v : View}
    {x : Option (Block Tx)} (hx : NoProgress f S v x) : NoProgress f S' v x :=
  hx.trans (Finset.card_le_card (noProgressWitnesses_subset h v x))

omit [DecidableEq Tx] in
theorem mem_noProgressWitnesses {S : Finset (Msg n Tx)} {v : View} {x : Option (Block Tx)}
    {q : Fin n} : q ∈ noProgressWitnesses S v x ↔ NoProgressWitness S v x q := by
  simp [noProgressWitnesses]

end Minimmit
