import Minimmit.Analysis.Responsiveness.Lemma5_8
import Minimmit.Analysis.Responsiveness.Lemma5_9

/-!
# Lemma 5.10（Optimistic responsiveness）

δ ≤ Δ は GST 以後の実際の遅延の上界。

## 論文からの差異

- リーダーの条件は「どの f_a + 1 個の連続する view にも正直なリーダーがいる」。f_a はこの
  条件のパラメータで、定理は f_a ≤ f を課さない。論文の f_a は実際に腐敗する人数で f 以下、
  論文の輪番 lead(v) = p_{(v mod n)+1} は f_a 人以下の腐敗のもとでこの条件を満たすので、
  論文の設定はこの条件の一例。
- 論文の O(·) は具体的な上界 t + δ + (f_a + 1)(2Δ + 3δ) + 3δ に置き換える。論文の証明は
  O(f_a Δ + δ) のままで数字を出さない。この上界は、取引が全正直者に届く t + δ に、Lemma 5.9
  の上界を f_a + 1 view 分と Lemma 5.8 の上界を足したもの。具体的な上界は O(·) の主張を含む。
- 上界に祖先が届くまでの時間は含まない。message がブロックの祖先を丸ごと運ぶので
  （Transition/Basic の「論文からの差異」）、論文の証明が最後に見積もる「correct processors
  receive all ancestors of b by t + O(f_a Δ + δ)」の分が要らない。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {GST : Time} {lead : View → Fin n} {s₀ : State n Tx}
  {instrs : Nat → Instr n Tx}

/-- Lemma 5.10（Optimistic responsiveness）: 取引 tr を正直者が初めて受け取るのが t ≥ GST
    なら、正直者は全員 t + δ + (f_a + 1)(2Δ + 3δ) + 3δ までに tr を finalise する。
    どの f_a + 1 個の連続する view にも正直なリーダーがいることを仮定する（論文の
    lead(v) = p_{(v mod n)+1} は f_a 人以下の腐敗のもとでこれを満たす）。 -/
theorem optimistic_responsiveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hδ : δ ≤ Δ) (hs : PartialSync δ GST s₀ instrs) {fa : Nat}
    (hlead : ∀ v : View, ∃ v' : View, v.val ≤ v'.val ∧ v'.val ≤ v.val + fa
      ∧ Correct s₀ instrs (lead v'))
    {i : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {tr : Tx}
    (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S)
    (hfirst : ∀ j t', Correct s₀ instrs j → t' < t →
      Msg.tx tr ∉ ((State.run s₀ instrs t').procs j).S)
    (hgst : GST.val ≤ t) :
    ∀ j, Correct s₀ instrs j → ∃ b : Block Tx,
      LNotarised f ((State.run s₀ instrs (t + δ + (fa + 1) * (2 * Δ + 3 * δ) + 3 * δ)).procs j).S b
      ∧ tr ∈ b.trStar := by
  classical
  have hδ1 := hs.one_le
  have hΔ1 : 1 ≤ Δ := le_trans hδ1 hδ
  -- tr は t + δ までに全正直者に届く
  have htx : ∀ r, Correct s₀ instrs r → ∀ T, t + δ ≤ T →
      Msg.tx tr ∈ ((State.run s₀ instrs T).procs r).S := fun r hr T hT =>
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
  -- v₀ + k の最初の入場は t + δ + k(2Δ + 3δ) 以前
  have hP : ∀ k, ∃ tk, FirstEntry s₀ instrs ⟨v₀.val + k⟩ tk ∧ tk ≤ t + δ + k * (2 * Δ + 3 * δ) := by
    intro k
    induction k with
    | zero =>
      refine ⟨Nat.find hreach₀, ⟨?_, ?_⟩, ?_⟩
      · obtain ⟨r, hr, h⟩ := Nat.find_spec hreach₀
        exact ⟨r, hr, h⟩
      · intro r t' hr h
        exact Nat.find_min' hreach₀ ⟨r, hr, h⟩
      · have := Nat.find_min' hreach₀ ⟨r₀, hr₀c,
          by rw [show t + δ - 1 + 1 = t + δ by omega, hv₀r]⟩
        omega
    | succ k ih =>
      obtain ⟨tk, hfk, hle⟩ := ih
      have hleave := leave_view_anchor hn hinit hh hb hδ hs (v := ⟨v₀.val + k⟩)
        (show 1 ≤ v₀.val + k by omega) hfk (T₀ := t + δ + k * (2 * Δ + 3 * δ)) hle (by omega)
      have hreach : ∃ s, ∃ r, Correct s₀ instrs r
          ∧ (⟨v₀.val + (k + 1)⟩ : View).val ≤ (viewAt s₀ instrs r (s + 1)).val := by
        refine ⟨t + δ + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ, i, hi, ?_⟩
        have h1 : v₀.val + k < (viewAt s₀ instrs i
            (t + δ + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ + 1)).val := hleave i hi
        show v₀.val + (k + 1) ≤ _
        omega
      refine ⟨Nat.find hreach,
        ⟨Nat.find_spec hreach, fun r t' hr h => Nat.find_min' hreach ⟨r, hr, h⟩⟩, ?_⟩
      have h1 := Nat.find_min' hreach (m := t + δ + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ) ⟨i, hi, by
        have h1 : v₀.val + k < (viewAt s₀ instrs i
            (t + δ + k * (2 * Δ + 3 * δ) + 2 * Δ + 3 * δ + 1)).val := hleave i hi
        show v₀.val + (k + 1) ≤ _
        omega⟩
      rw [Nat.add_mul, Nat.one_mul]
      omega
  -- v₁: v₀ + 1 以上 v₀ + 1 + f_a 以下の、正直なリーダーの view
  obtain ⟨v₁, hv₁ge, hv₁le, hlc⟩ := hlead ⟨v₀.val + 1⟩
  have hv₁ge' : v₀.val + 1 ≤ v₁.val := hv₁ge
  have hv₁le' : v₁.val ≤ v₀.val + 1 + fa := hv₁le
  obtain ⟨tm, hfm, hlem⟩ := hP (v₁.val - v₀.val)
  have hv₁eq : (⟨v₀.val + (v₁.val - v₀.val)⟩ : View) = v₁ :=
    View.val_injective (by show v₀.val + (v₁.val - v₀.val) = v₁.val; omega)
  rw [hv₁eq] at hfm
  have hv₁1 : 1 ≤ v₁.val := by omega
  -- v₁ への最初の入場は t + δ 以降
  have htm : t + δ ≤ tm := by
    obtain ⟨r, hr, h⟩ := hfm.entered
    by_contra hlt
    have h1 := viewAt_mono (s₀ := s₀) (instrs := instrs) r (show tm + 1 ≤ t + δ by omega)
    have h2 := hbound r hr
    omega
  obtain ⟨e, R⟩ := leader_round hinit hh hs hδ hv₁1 hlc hfm (by omega)
  have hte := first_entry_le_leader_entry R
  have hmul : (v₁.val - v₀.val) * (2 * Δ + 3 * δ) ≤ (fa + 1) * (2 * Δ + 3 * δ) :=
    Nat.mul_le_mul_right _ (by omega)
  intro j hj
  refine ⟨leaderBlockAt f lead s₀ instrs v₁ e, ?_, ?_⟩
  · exact (leaderBlock_lnotarised_by (j := j) hinit hh hb hs R).mono
      (S_subset_run s₀ instrs j (by omega))
  · apply mem_trStar_leaderBlock
    apply Algo.S_subset_st1 f (lead v₁) _
    exact htx (lead v₁) hlc e (by omega)

end Minimmit
