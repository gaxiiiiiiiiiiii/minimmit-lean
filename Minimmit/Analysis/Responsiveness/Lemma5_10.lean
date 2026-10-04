import Minimmit.Analysis.Responsiveness.Lemma5_8
import Minimmit.Analysis.Responsiveness.Lemma5_9
import Minimmit.Analysis.Latency

/-!
# Lemma 5.10（Optimistic responsiveness）

δ ≤ Δ は GST 以後の実際の遅延の上界。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {GST : Time} {lead : View → Fin n} {s₀ : State n Tx}
  {instrs : Nat → Instr n Tx}

/-- 正直者が初めて view w に入る時刻が T 以下で GST ≤ T なら、view w + k に初めて入る時刻は
    T + k(2Δ + 3δ) 以下。各 view を Lemma 5.9 の一般形で離れる。 -/
theorem first_entries_chain (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ GST s₀ instrs) {w : Nat} (hw : 1 ≤ w)
    {T : Nat} (hgst : GST.val ≤ T) {t0 : Nat} (h0 : FirstEntry s₀ instrs ⟨w⟩ t0) (ht0 : t0 ≤ T) :
    ∀ k, ∃ tk, FirstEntry s₀ instrs ⟨w + k⟩ tk ∧ tk ≤ T + k * (2 * Δ + 3 * δ) := by
  classical
  intro k
  induction k with
  | zero => exact ⟨t0, h0, by omega⟩
  | succ k ih =>
    obtain ⟨tk, hfk, hle⟩ := ih
    obtain ⟨i, hi, _⟩ := hfk.entered
    have hleave := leave_view_anchor hn hinit hh hb hδ hs (v := ⟨w + k⟩)
      (show 1 ≤ w + k by omega) hfk (T₀ := T + k * (2 * Δ + 3 * δ)) hle (by omega)
    have hreach : ∃ s, ∃ r, Correct s₀ instrs r
        ∧ (⟨w + (k + 1)⟩ : View).val ≤ (viewAt s₀ instrs r (s + 1)).val := by
      refine ⟨T + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ, i, hi, ?_⟩
      have h1 : w + k < (viewAt s₀ instrs i
          (T + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ + 1)).val := hleave i hi
      show w + (k + 1) ≤ _
      omega
    refine ⟨Nat.find hreach, firstEntry_of_reach hinit (show 1 ≤ w + (k + 1) by omega) hreach, ?_⟩
    have h1 := Nat.find_min' hreach (m := T + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ) ⟨i, hi, by
      have h1 : w + k < (viewAt s₀ instrs i
          (T + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ + 1)).val := hleave i hi
      show w + (k + 1) ≤ _
      omega⟩
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Lemma 5.10 の核: 取引 tr を正直者が初めて受け取るのが t ≥ GST なら、正直者は全員
    t + f_a(2Δ + 3δ) + 8δ までに tr を finalise する。t + δ に進行中の最大の view v₀ を、
    lead(v₀) が正直なら 5.8 の一般形で 4δ、そうでなければ 5.9 の一般形で 2Δ + 3δ で離れ、
    以後は正直なリーダーの view v₁ まで f_a 個以下の view を 5.9 で通過し、v₁ で 5.8 により
    finalise する。 -/
theorem tx_finalised_by (hprot : IsMinimmit f Δ lead GST s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ GST s₀ instrs) {fa : Nat}
    (hlead : CorrectLeaderWithin s₀ instrs lead fa)
    {i : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {tr : Tx}
    (htr : Msg.tx tr ∈ ((State.stateAt s₀ instrs t).procs i).S)
    (hfirst : ∀ j t', Correct s₀ instrs j → t' < t →
      Msg.tx tr ∉ ((State.stateAt s₀ instrs t').procs j).S)
    (hgst : GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j → ∃ b : Block n Tx,
      Finalised f ((State.stateAt s₀ instrs (t + fa * (2 * Δ + 3 * δ) + 8 * δ)).procs j).S b
      ∧ tr ∈ b.trStar := by
  classical
  have ⟨hn, hinit, hh, hb, _, _⟩ := hprot
  have hδ1 := hs.one_le
  have hΔ1 : 1 ≤ Δ := le_trans hδ1 hδ
  -- tr は t + δ までに全正直者に届く
  have htx : ∀ r, Correct s₀ instrs r → ∀ T, t + δ ≤ T →
      Msg.tx tr ∈ ((State.stateAt s₀ instrs T).procs r).S := fun r hr T hT =>
    delivered hinit hh hs hi (tx_forwarded hinit hh hi htr (fun t' ht' => hfirst i t' hi ht') r)
      (by omega) (by omega)
  -- v₀: t + δ における正直者の view の最大
  have hne : (correctSet s₀ instrs).Nonempty := ⟨i, mem_correctSet.mpr hi⟩
  obtain ⟨r₀, hr₀, hv₀⟩ := Finset.exists_mem_eq_sup (correctSet s₀ instrs) hne
    (fun r => (viewAt s₀ instrs r (t + δ)).val)
  have hr₀c := mem_correctSet.mp hr₀
  set v₀ : View := ⟨(correctSet s₀ instrs).sup fun r => (viewAt s₀ instrs r (t + δ)).val⟩
    with hv₀def
  have hbound : ∀ r, Correct s₀ instrs r → (viewAt s₀ instrs r (t + δ)).val ≤ v₀.val :=
    fun r hr => Finset.le_sup (f := fun r => (viewAt s₀ instrs r (t + δ)).val)
    (mem_correctSet.mpr hr)
  have hv₀1 : 1 ≤ v₀.val := le_trans (viewAt_pos hinit hh hi (t + δ)) (hbound i hi)
  have hv₀r : v₀.val = (viewAt s₀ instrs r₀ (t + δ)).val := hv₀
  have hreach₀ : ∃ s, ∃ r, Correct s₀ instrs r ∧ v₀.val ≤ (viewAt s₀ instrs r (s + 1)).val :=
    ⟨t + δ - 1, r₀, hr₀c, by rw [show t + δ - 1 + 1 = t + δ by omega, hv₀r]⟩
  have hfe₀ : FirstEntry s₀ instrs v₀ (Nat.find hreach₀) := firstEntry_of_reach hinit hv₀1 hreach₀
  have hfe₀le : Nat.find hreach₀ ≤ t + δ - 1 :=
    Nat.find_min' hreach₀ ⟨r₀, hr₀c, by rw [show t + δ - 1 + 1 = t + δ by omega, hv₀r]⟩
  -- v₁: v₀ より後で最初の正直なリーダーの view と、正直者が初めて v₁ に入る時刻の上界
  have key : ∃ v₁ : View, v₀.val < v₁.val ∧ Correct s₀ instrs (lead v₁) ∧
      ∃ tm, FirstEntry s₀ instrs v₁ tm ∧ tm ≤ t + 5 * δ + fa * (2 * Δ + 3 * δ) := by
    by_cases hlc₀ : Correct s₀ instrs (lead v₀)
    · -- lead(v₀) が正直: v₀ を t + 5δ までに離れ、v₀ + 1 以上 v₀ + 1 + f_a 以下に正直なリーダー
      have hleave := leave_view_fast_anchor hn hinit hh hb hδ hs hv₀1 hlc₀ hfe₀
        (T₀ := t + δ) (by omega) (by omega)
      have hreach₁ : ∃ s, ∃ r, Correct s₀ instrs r
          ∧ (⟨v₀.val + 1⟩ : View).val ≤ (viewAt s₀ instrs r (s + 1)).val :=
        ⟨t + 5 * δ, i, hi, by
          have h1 : v₀.val < (viewAt s₀ instrs i (t + δ + 4 * δ + 1)).val := hleave i hi
          show v₀.val + 1 ≤ _
          rw [show t + 5 * δ + 1 = t + δ + 4 * δ + 1 by omega]
          omega⟩
      have hfe₁ := firstEntry_of_reach hinit (show 1 ≤ v₀.val + 1 by omega) hreach₁
      have hfe₁le : Nat.find hreach₁ ≤ t + 5 * δ := Nat.find_min' hreach₁ ⟨i, hi, by
        have h1 : v₀.val < (viewAt s₀ instrs i (t + δ + 4 * δ + 1)).val := hleave i hi
        show v₀.val + 1 ≤ _
        rw [show t + 5 * δ + 1 = t + δ + 4 * δ + 1 by omega]
        omega⟩
      obtain ⟨v₁, hv₁ge, hv₁le, hlc⟩ := hlead ⟨v₀.val + 1⟩
      have hv₁ge' : v₀.val + 1 ≤ v₁.val := hv₁ge
      have hv₁le' : v₁.val ≤ v₀.val + 1 + fa := hv₁le
      obtain ⟨tm, hfm, hlem⟩ := first_entries_chain hn hinit hh hb hδ hs (w := v₀.val + 1)
        (by omega) (T := t + 5 * δ) (by omega) hfe₁ hfe₁le (v₁.val - (v₀.val + 1))
      have hv₁eq : (⟨v₀.val + 1 + (v₁.val - (v₀.val + 1))⟩ : View) = v₁ :=
        View.val_injective (by show v₀.val + 1 + (v₁.val - (v₀.val + 1)) = v₁.val; omega)
      rw [hv₁eq] at hfm
      refine ⟨v₁, by omega, hlc, tm, hfm, ?_⟩
      have hmul : (v₁.val - (v₀.val + 1)) * (2 * Δ + 3 * δ) ≤ fa * (2 * Δ + 3 * δ) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · -- lead(v₀) が Byzantine: v₀ 以上 v₀ + f_a 以下に正直なリーダーがいて、v₀ ではない
      obtain ⟨v₁, hv₁ge, hv₁le, hlc⟩ := hlead v₀
      have hv₁ge' : v₀.val ≤ v₁.val := hv₁ge
      have hv₁le' : v₁.val ≤ v₀.val + fa := hv₁le
      have hgt : v₀.val < v₁.val := by
        rcases lt_or_eq_of_le hv₁ge' with h | h
        · exact h
        · exact absurd (View.val_injective h ▸ hlc) hlc₀
      obtain ⟨tm, hfm, hlem⟩ := first_entries_chain hn hinit hh hb hδ hs (w := v₀.val) hv₀1
        (T := t + δ) (by omega) hfe₀ (by omega) (v₁.val - v₀.val)
      have hv₁eq : (⟨v₀.val + (v₁.val - v₀.val)⟩ : View) = v₁ :=
        View.val_injective (by show v₀.val + (v₁.val - v₀.val) = v₁.val; omega)
      rw [hv₁eq] at hfm
      refine ⟨v₁, hgt, hlc, tm, hfm, ?_⟩
      have hmul : (v₁.val - v₀.val) * (2 * Δ + 3 * δ) ≤ fa * (2 * Δ + 3 * δ) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  obtain ⟨v₁, hgt, hlc, tm, hfm, hlem⟩ := key
  have hv₁1 : 1 ≤ v₁.val := by omega
  -- 正直者が最初に v₁ に入るのは t + δ 以降
  have htm : t + δ ≤ tm := by
    obtain ⟨r, hr, h⟩ := hfm.entered_ge
    by_contra hlt
    have h1 := viewAt_mono (s₀ := s₀) (instrs := instrs) r (show tm + 1 ≤ t + δ by omega)
    have h2 := hbound r hr
    omega
  obtain ⟨e, R⟩ := leader_round hn hinit hh hb hs hδ hv₁1 hlc hfm (by omega)
  have hte := first_entry_le_leader_entry hinit R
  intro j hj
  refine ⟨leaderBlockAt f lead s₀ instrs v₁ e, ?_, ?_⟩
  · exact (leaderBlock_finalised_by (j := j) hinit hh hb hs R).mono
      (S_subset_stateAt s₀ instrs j (by omega))
  · apply mem_trStar_leaderBlock
    apply Algo.S_subset_st1 f (lead v₁) _
    exact htx (lead v₁) hlc e (by omega)

/-- Lemma 5.10（Optimistic responsiveness）: Minimmit は optimistically responsive。定数は 8。 -/
theorem optimistic_responsiveness : OptimisticallyResponsive := by
  classical
  refine ⟨8, ?_⟩
  intro n Tx _ f Δ δ fa GST lead s₀ instrs hprot hδ hs hlead t tr hrecv hgst
  obtain ⟨⟨i, hi, htr⟩, hfirst⟩ := hrecv
  -- 期限までに全員が finalise している
  have hB : FinalisedByAll f s₀ instrs tr (t + 8 * (fa * Δ + δ)) := by
    intro j hj
    obtain ⟨b, hb, hmem⟩ := tx_finalised_by hprot hδ hs hlead hi htr hfirst hgst j hj
    refine ⟨b, hb.mono (S_subset_stateAt s₀ instrs j ?_), hmem⟩
    rw [Nat.mul_add fa (2 * Δ) (3 * δ), Nat.mul_left_comm fa 2 Δ, Nat.mul_left_comm fa 3 δ]
    have h1 : fa * δ ≤ fa * Δ := Nat.mul_le_mul_left fa hδ
    omega
  -- 初めて全員が finalise している ℓ をとる
  have hex : ∃ ℓ, FinalisedByAll f s₀ instrs tr (t + ℓ) := ⟨_, hB⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hB, t, ⟨⟨i, hi, htr⟩, hfirst⟩, Nat.find_spec hex,
    fun ℓ' hℓ' => Nat.find_min hex hℓ'⟩

end Minimmit
