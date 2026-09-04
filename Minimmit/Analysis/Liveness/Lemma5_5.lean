import Minimmit.Analysis.Liveness.Timing

/-!
# Lemma 5.5（Progression through views）

正直者はすべての view に入る。view k で止まる正直者がいれば、他の正直者も止まり、
全員が timeout で投票か nullify を出し、進捗のなさの証拠から全員が nullify を出して
nullification ができ、止まれない。

## 論文からの差異

- 論文の「view v に入る」を「view v 以上に達する」として述べる。登り切りでは 1 スロットで
  v を通り過ぎることがあり、スロットの冒頭に v にいるとは限らない。view は 1 ずつしか
  進まないので、v 以上に達したプロセッサは v を通過している。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]
variable {f Δ δ : Nat} {lead : View → Fin n} {s₀ : State n Tx} {instrs : Nat → Instr n Tx}

/-- 「最初の正直者が view v に入るのはスロット t」: スロット t を終えて view が v 以上に
    なった正直者がいて、それより前のスロットではいない。v = 1 なら t = 0。 -/
structure FirstEntry (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (v : View) (t : Nat) :
    Prop where
  entered : ∃ i, Correct s₀ instrs i ∧ v.val ≤ (viewAt s₀ instrs i (t + 1)).val
  first : ∀ i t', Correct s₀ instrs i → v.val ≤ (viewAt s₀ instrs i (t' + 1)).val → t ≤ t'

/-! ### 5.5 の補題 -/

theorem viewAt_pos (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) (t : Nat) : 1 ≤ (viewAt s₀ instrs i t).val :=
  (localInv_run hinit hh hi t).view_pos

/-- 正直者の集合。 -/
noncomputable def correctSet (s₀ : State n Tx) (instrs : Nat → Instr n Tx) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (Correct s₀ instrs)

theorem mem_correctSet {j : Fin n} : j ∈ correctSet s₀ instrs ↔ Correct s₀ instrs j := by
  classical
  simp [correctSet]

/-- 正直者は n − f 人以上。 -/
theorem card_correctSet (hb : ByzBound f s₀ instrs) : n - f ≤ (correctSet s₀ instrs).card := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (Correct s₀ instrs)
  have h2 : (Finset.univ.filter (fun q => ¬ Correct s₀ instrs q)).card ≤ f :=
    card_le_of_byz hb _ fun q hq => exists_byz_of_not_correct (Finset.mem_filter.mp hq).2
  have h3 : (correctSet s₀ instrs).card = (Finset.univ.filter (Correct s₀ instrs)).card := by
    simp [correctSet]
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- 正直者 p_j が t + 1 の S に持つ自分の署名付き message は、正直者 p_i に期限までに届く。 -/
theorem own_delivered (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) (hs : PartialSync δ s₀ instrs)
    {i j : Fin n} (_hi : Correct s₀ instrs i) (hj : Correct s₀ instrs j) {s : Nat} {m : Msg n Tx}
    (hm : m ∈ ((State.run s₀ instrs (s + 1)).procs j).S) (hsig : m.signer = some j) {T : Nat}
    (hT₁ : s + 1 ≤ T) (hT₂ : max hs.GST.val s + δ ≤ T) : m ∈ ((State.run s₀ instrs T).procs i).S := by
  obtain ⟨t', ht', j', hj'⟩ := sendsBefore_of_mem_S hinit hm hsig
  have hact := hh t' j (hj t')
  have hsend : Action.send m i ∈ (instrs t').actions j := by
    rw [hact] at hj' ⊢
    exact Algo.send_all hj' i
  exact delivered hinit hh hs hj hsend (by omega)
    ((Nat.add_le_add_right (max_le_max (le_refl _) (Nat.le_of_lt_succ ht')) δ).trans hT₂)

theorem viewAt_zero (hinit : Init s₀) (j : Fin n) : (viewAt s₀ instrs j 0).val = 1 := by
  unfold viewAt; rw [State.run, hinit.procs j]; rfl


/-- 正直者 p_i が view k で止まり続けるなら、他の正直者も view k を越えない。越えたなら
    その証明書が p_i に届いて p_i も進むから。 -/
theorem stuck_all (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) (hs : PartialSync Δ s₀ instrs)
    {i : Fin n} (hi : Correct s₀ instrs i) {k : Nat} (hk : 1 ≤ k)
    (hstuck : ∀ t, (viewAt s₀ instrs i t).val ≤ k) (hreach : ∃ t₀, k ≤ (viewAt s₀ instrs i t₀).val)
    {j : Fin n} (hj : Correct s₀ instrs j) : ∀ t, (viewAt s₀ instrs j t).val ≤ k := by
  classical
  by_contra hcon
  simp only [not_forall, not_le] at hcon
  obtain ⟨t₀, ht₀⟩ := hreach
  have hex : ∃ t, k < (viewAt s₀ instrs j t).val := hcon
  have hspec := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, viewAt_zero hinit] at hspec
    omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_one_of_ne_zero hpos
  have hle : (viewAt s₀ instrs j t).val ≤ (⟨k⟩ : View).val :=
    not_lt.mp (Nat.find_min hex (by rw [ht]; exact Nat.lt_succ_self t))
  have hlt : (⟨k⟩ : View).val < (viewAt s₀ instrs j (t + 1)).val := by rw [← ht]; exact hspec
  -- i が view k にいるスロット T で証明書を持つ
  have hvT : ∀ T, t₀ ≤ T → viewAt s₀ instrs i T = ⟨k⟩ := fun T hT =>
    View.val_injective (le_antisymm (hstuck T) (ht₀.trans (viewAt_mono i hT)))
  rcases leave_view_cert hh hj hle hlt with hN | ⟨b, hbv, hM⟩
  · have hNi := nullified_all hinit hh hs hj hi hN
      (T := max (max hs.GST.val (t + 1) + Δ) (max (t + 2) t₀)) (by omega) (by omega)
    have := leave_of_nullified hh hi (hvT _ (by omega)) hNi
    exact absurd (hstuck _) (not_le.mpr this)
  · have hg : b ≠ .gen := by
      intro h; subst h; simp [Block.view] at hbv; omega
    have hMi := mnotarised_all hinit hh hs hj hi hM
      (T := max (max hs.GST.val (t + 1) + Δ) (max (t + 2) t₀)) (by omega) (by omega)
    have := leave_of_mnotarised hh hi ((hvT _ (by omega)).trans hbv.symm) hg hMi
    rw [hbv] at this
    exact absurd (hstuck _) (not_le.mpr this)

/-- view k に止まる正直者は、timer が 2Δ に達したスロット s で、view k のブロックに投票済みか
    nullify(k) を送っている。 -/
theorem timeout_stuck (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) (hs : PartialSync Δ s₀ instrs)
    {j : Fin n} (hj : Correct s₀ instrs j) {k : Nat} (hreach : ∃ t, k ≤ (viewAt s₀ instrs j t).val)
    (hstuck : ∀ t, (viewAt s₀ instrs j t).val ≤ k) :
    ∃ s, k ≤ (viewAt s₀ instrs j s).val
      ∧ ((∃ b, b.view = ⟨k⟩ ∧ Msg.vote j b ∈ ((State.run s₀ instrs (s + 1)).procs j).S)
        ∨ Msg.nullify j ⟨k⟩ ∈ ((State.run s₀ instrs (s + 1)).procs j).S) := by
  classical
  have hex := hreach
  have he : (viewAt s₀ instrs j (Nat.find hex)).val = k :=
    le_antisymm (hstuck _) (Nat.find_spec hex)
  have hstay : ∀ m, viewAt s₀ instrs j (Nat.find hex + m) = viewAt s₀ instrs j (Nat.find hex) :=
    fun m => View.val_injective (le_antisymm (by rw [he]; exact hstuck _)
      (viewAt_mono j (Nat.le_add_right _ m)))
  have htimer : timerAt s₀ instrs j (Nat.find hex) ≤ 1 := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]
      show ((State.run s₀ instrs 0).procs j).timer ≤ 1
      rw [State.run, hinit.procs j]; exact Nat.zero_le 1
    · obtain ⟨e', he'⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hlt : (viewAt s₀ instrs j e').val < k :=
        not_le.mp (Nat.find_min hex (by rw [he']; exact Nat.lt_succ_self e'))
      rcases timerAt_succ (s₀ := s₀) (instrs := instrs) j e' with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [he']; exact h1.le
      · exfalso
        rw [← he'] at h2
        have := congrArg View.val h2
        rw [he] at this
        omega
  have h2Δ := hs.one_le
  have h2 : timerAt s₀ instrs j (Nat.find hex + (2 * Δ - timerAt s₀ instrs j (Nat.find hex))) = 2 * Δ := by
    rw [timerAt_add j _ _ (fun k' _ => hstay k')]
    omega
  refine ⟨Nat.find hex + (2 * Δ - timerAt s₀ instrs j (Nat.find hex)), ?_, ?_⟩
  · rw [hstay, he]
  · rcases timeout hinit hh hj (v := ⟨k⟩) (View.val_injective (by rw [hstay, he])) h2 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have h' : k < (viewAt s₀ instrs j (Nat.find hex + (2 * Δ - timerAt s₀ instrs j (Nat.find hex)) + 1)).val := h
      have := hstuck (Nat.find hex + (2 * Δ - timerAt s₀ instrs j (Nat.find hex)) + 1)
      omega

/-- 5.5 の本体: すべての正直者が、すべての k について view k 以上に達する。 -/
theorem progression_aux (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs) (hs : PartialSync Δ s₀ instrs) :
    ∀ k : Nat, ∀ i, Correct s₀ instrs i → ∃ t, k ≤ (viewAt s₀ instrs i t).val := by
  intro k
  induction k with
  | zero => intro i _; exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
    intro i hi
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    have hstuck : ∀ t, (viewAt s₀ instrs i t).val ≤ k := fun t => Nat.lt_succ_iff.mp (hcon t)
    have hk : 1 ≤ k := le_trans (viewAt_pos hinit hh hi 0) (hstuck 0)
    have hall : ∀ j, Correct s₀ instrs j → ∀ t, (viewAt s₀ instrs j t).val ≤ k :=
      fun j hj => stuck_all hinit hh hs hi hk hstuck (ih i hi) hj
    have hto : ∀ j, Correct s₀ instrs j → ∃ s, k ≤ (viewAt s₀ instrs j s).val
        ∧ ((∃ b, b.view = ⟨k⟩ ∧ Msg.vote j b ∈ ((State.run s₀ instrs (s + 1)).procs j).S)
          ∨ Msg.nullify j ⟨k⟩ ∈ ((State.run s₀ instrs (s + 1)).procs j).S) :=
      fun j hj => timeout_stuck hinit hh hs hj (ih j hj) (hall j hj)
    classical
    let sf : Fin n → Nat := fun j =>
      if h : Correct s₀ instrs j then Classical.choose (hto j h) else 0
    have hsf : ∀ j (hj : Correct s₀ instrs j), k ≤ (viewAt s₀ instrs j (sf j)).val
        ∧ ((∃ b, b.view = ⟨k⟩ ∧ Msg.vote j b ∈ ((State.run s₀ instrs (sf j + 1)).procs j).S)
          ∨ Msg.nullify j ⟨k⟩ ∈ ((State.run s₀ instrs (sf j + 1)).procs j).S) := by
      intro j hj
      simp only [sf, dif_pos hj]
      exact Classical.choose_spec (hto j hj)
    have hC := card_correctSet (s₀ := s₀) (instrs := instrs) hb
    have hT₂ : ∀ j ∈ correctSet s₀ instrs,
        sf j + 1 ≤ max hs.GST.val ((correctSet s₀ instrs).sup sf) + Δ + 1
        ∧ max hs.GST.val (sf j) + Δ ≤ max hs.GST.val ((correctSet s₀ instrs).sup sf) + Δ + 1 := by
      intro j hj
      have := Finset.le_sup (f := sf) hj
      omega
    set T₂ := max hs.GST.val ((correctSet s₀ instrs).sup sf) + Δ + 1 with hT₂def
    -- T₂ 以降、正直者は全員 view k
    have hview : ∀ j, Correct s₀ instrs j → ∀ t, T₂ ≤ t → viewAt s₀ instrs j t = ⟨k⟩ := by
      intro j hj t ht
      have h1 := (hsf j hj).1
      have h2 := (hT₂ j (mem_correctSet.mpr hj)).1
      exact View.val_injective (le_antisymm (hall j hj t) (h1.trans (viewAt_mono j (by omega))))
    -- T₂ には全正直者の投票か nullify が全正直者に届いている
    have hmsg : ∀ j ∈ correctSet s₀ instrs, ∀ i' ∈ correctSet s₀ instrs,
        (∃ b, b.view = ⟨k⟩ ∧ Msg.vote j b ∈ ((State.run s₀ instrs T₂).procs i').S)
          ∨ Msg.nullify j ⟨k⟩ ∈ ((State.run s₀ instrs T₂).procs i').S := by
      intro j hj i' hi'
      have hjc := mem_correctSet.mp hj
      have hi'c := mem_correctSet.mp hi'
      rcases (hsf j hjc).2 with ⟨b, hbv, hm⟩ | hm
      · exact Or.inl ⟨b, hbv, own_delivered hinit hh hs hi'c hjc hm rfl (hT₂ j hj).1 (hT₂ j hj).2⟩
      · exact Or.inr (own_delivered hinit hh hs hi'c hjc hm rfl (hT₂ j hj).1 (hT₂ j hj).2)
    -- 全正直者が T₂ + 1 までに nullify(k) を送る
    have hnull : ∀ j ∈ correctSet s₀ instrs,
        Msg.nullify j ⟨k⟩ ∈ ((State.run s₀ instrs (T₂ + 1)).procs j).S := by
      intro j hj
      have hjc := mem_correctSet.mp hj
      rcases (hsf j hjc).2 with ⟨b, hbv, hm⟩ | hm
      · have hvT : viewAt s₀ instrs j T₂ = ⟨k⟩ := hview j hjc T₂ (le_refl _)
        have hmT : Msg.vote j b ∈ ((State.run s₀ instrs T₂).procs j).S :=
          S_subset_run s₀ instrs j (hT₂ j hj).1 hm
        have hL := localInv_run hinit hh hjc T₂
        have hnot : ((State.run s₀ instrs T₂).procs j).notarised = some b := by
          refine ((hL.notar b hmT).2.resolve_left ?_).2
          rw [hbv]
          change ¬ k < (viewAt s₀ instrs j T₂).val
          rw [hvT]; exact lt_irrefl _
        have hg : b ≠ .gen := by
          intro h; subst h; simp [Block.view] at hbv; omega
        have hnoM : ¬ MNotarised f ((State.run s₀ instrs T₂).procs j).S b := by
          intro hM
          have := leave_of_mnotarised hh hjc (hvT.trans hbv.symm) hg hM
          rw [hbv] at this
          exact absurd (hall j hjc (T₂ + 1)) (not_le.mpr this)
        have hvoters : (voters ((State.run s₀ instrs T₂).procs j).S b).card ≤ 2 * f := by
          by_contra h
          exact hnoM (Or.inr (not_le.mp h))
        have hnp : NoProgress f ((State.run s₀ instrs T₂).procs j).S ⟨k⟩ (some b) := by
          have hCsub : correctSet s₀ instrs ⊆
              (correctSet s₀ instrs).filter
                (fun c => NoProgressWitness ((State.run s₀ instrs T₂).procs j).S ⟨k⟩ (some b) c)
              ∪ (correctSet s₀ instrs).filter
                (fun c => Msg.vote c b ∈ ((State.run s₀ instrs T₂).procs j).S) := by
            intro c hc
            rcases hmsg c hc j hj with ⟨b', hb'v, hm'⟩ | hm'
            · by_cases hbb : b' = b
              · subst hbb
                exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc, hm'⟩)
              · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
                  ⟨hc, .vote b' hb'v (fun h => hbb (Option.some.inj h)) hm'⟩)
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, .nullify hm'⟩)
          have hV : ((correctSet s₀ instrs).filter
              (fun c => Msg.vote c b ∈ ((State.run s₀ instrs T₂).procs j).S)).card ≤ 2 * f :=
            (Finset.card_le_card fun c hc => mem_voters.mpr (Finset.mem_filter.mp hc).2).trans hvoters
          have hW : (correctSet s₀ instrs).filter
              (fun c => NoProgressWitness ((State.run s₀ instrs T₂).procs j).S ⟨k⟩ (some b) c)
              ⊆ noProgressWitnesses ((State.run s₀ instrs T₂).procs j).S ⟨k⟩ (some b) :=
            fun c hc => mem_noProgressWitnesses.mpr (Finset.mem_filter.mp hc).2
          have h1 := Finset.card_le_card hCsub
          have h2 := Finset.card_union_le ((correctSet s₀ instrs).filter
              (fun c => NoProgressWitness ((State.run s₀ instrs T₂).procs j).S ⟨k⟩ (some b) c))
            ((correctSet s₀ instrs).filter
              (fun c => Msg.vote c b ∈ ((State.run s₀ instrs T₂).procs j).S))
          have h4 := Finset.card_le_card hW
          unfold NoProgress
          omega
        rcases noprogress_reaction hinit hh hjc hvT hnot hnp with h | h
        · exact h
        · exact absurd (hall j hjc (T₂ + 1)) (not_le.mpr h)
      · exact S_subset_run s₀ instrs j (by have := (hT₂ j hj).1; omega) hm
    -- nullification が i に届き、i が進む
    have hN : Nullified f ((State.run s₀ instrs (max hs.GST.val (T₂ + 1) + Δ + 1)).procs i).S ⟨k⟩ := by
      have hsub : correctSet s₀ instrs
          ⊆ nullifiers ((State.run s₀ instrs (max hs.GST.val (T₂ + 1) + Δ + 1)).procs i).S ⟨k⟩ :=
        fun j hj => mem_nullifiers.mpr (own_delivered hinit hh hs hi (mem_correctSet.mp hj)
          (hnull j hj) rfl (by omega) (by omega))
      have := Finset.card_le_card hsub
      unfold Nullified
      omega
    have hvT₃ : viewAt s₀ instrs i (max hs.GST.val (T₂ + 1) + Δ + 1) = ⟨k⟩ :=
      hview i hi _ (by omega)
    have := leave_of_nullified hh hi hvT₃ hN
    exact absurd (hstuck _) (not_le.mpr this)

/-- Lemma 5.5（Progression through views）: 正直者はすべての view に入る。 -/
theorem progression (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hs : PartialSync Δ s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i) (v : View) :
    ∃ t, v.val ≤ (viewAt s₀ instrs i t).val :=
  progression_aux hn hinit hh hb hs v.val i hi

end Minimmit
