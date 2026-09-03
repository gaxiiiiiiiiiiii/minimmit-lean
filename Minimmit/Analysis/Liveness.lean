import Minimmit.Analysis.Timing

/-!
# Liveness（§5.2）

Lemma 5.5〜5.7。部分同期を仮定する。
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

/-- 正直者 j の view が v を越えるなら、v から越えるスロットがある。 -/
theorem exists_leave_slot (hinit : Init s₀) {j : Fin n} {v : View} {t₁ : Nat} (hv : 1 ≤ v.val)
    (h : v.val < (viewAt s₀ instrs j t₁).val) :
    ∃ s < t₁, (viewAt s₀ instrs j s).val ≤ v.val ∧ v.val < (viewAt s₀ instrs j (s + 1)).val := by
  classical
  obtain ⟨t', rfl⟩ : ∃ t', t₁ = t' + 1 := by
    rcases t₁ with _ | t'
    · rw [viewAt_zero hinit] at h; omega
    · exact ⟨t', rfl⟩
  have hex : ∃ s, v.val < (viewAt s₀ instrs j (s + 1)).val := ⟨t', h⟩
  refine ⟨Nat.find hex, Nat.lt_succ_of_le (Nat.find_min' hex h), ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, viewAt_zero hinit]; exact hv
  · obtain ⟨s', hs'⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    rw [hs']
    exact not_lt.mp (Nat.find_min hex (by rw [hs']; exact Nat.lt_succ_self s'))

/-- 正直者がスロット s に view w の証明書を持てば、正直者は全員、期限までにそれを持つ。 -/
theorem hasCert_all (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) (hs : PartialSync δ s₀ instrs)
    {j : Fin n} (hj : Correct s₀ instrs j) {s : Nat} {w : View} (hw : 1 ≤ w.val)
    (h : Algo.HasCert f ((State.run s₀ instrs s).procs j).S w) {q : Fin n} (hq : Correct s₀ instrs q)
    {T : Nat} (hT₁ : s + 1 ≤ T) (hT₂ : max hs.GST.val s + δ ≤ T) :
    Algo.HasCert f ((State.run s₀ instrs T).procs q).S w := by
  rcases h with h | h
  · exact Or.inl (nullified_all hinit hh hs hj hq h hT₁ hT₂)
  · obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨hbv, hM⟩ := Algo.mem_mNotarisedAt hb
    have hg : b ≠ .gen := by
      intro hg
      subst hg
      have : w.val = 0 := by rw [← hbv]; rfl
      omega
    have := mnotarised_all hinit hh hs hj hq hM hT₁ hT₂
    rw [← hbv]
    exact Algo.hasCert_of_mnotarised hg this

/-- Lemma 5.6 の第 1 段: 最初の正直者が t に view v に入れば、正直者は全員
    max(t, GST) + δ までに view v に入る。T₀ は t 以上で GST 以上の任意の時刻。 -/
theorem enter_all_anchor (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hs : PartialSync δ s₀ instrs) {v : View} {t : Nat} (hfirst : FirstEntry s₀ instrs v t)
    {T₀ : Nat} (ht : t ≤ T₀) (hgst : hs.GST.val ≤ T₀) {q : Fin n} (hq : Correct s₀ instrs q) :
    v.val ≤ (viewAt s₀ instrs q (T₀ + δ + 1)).val := by
  obtain ⟨j, hj, hjv⟩ := hfirst.entered
  have hδ1 := hs.one_le
  rw [viewAt_succ_eq hh hq (T₀ + δ)]
  apply Algo.st1_reaches q
  intro w h1 h2
  have hw1 : 1 ≤ w.val := le_trans (viewAt_pos hinit hh hq (T₀ + δ)) h1
  obtain ⟨s, hs_lt, hs1, hs2⟩ := exists_leave_slot hinit hw1 (lt_of_lt_of_le h2 hjv)
  have hcert : Algo.HasCert f ((State.run s₀ instrs s).procs j).S w := by
    rw [viewAt_succ_eq hh hj s] at hs2
    exact Algo.st1_certs hs1 hs2
  exact hasCert_all hinit hh hs hj hw1 hcert hq (by omega) (by omega)

/-- 最初の正直者が t ≥ GST に view v に入れば、正直者は全員 t + δ までに view v に入る。 -/
theorem enter_all (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) (hs : PartialSync δ s₀ instrs)
    {v : View} {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : hs.GST.val ≤ t) {q : Fin n}
    (hq : Correct s₀ instrs q) : v.val ≤ (viewAt s₀ instrs q (t + δ + 1)).val :=
  enter_all_anchor hinit hh hs hfirst (le_refl t) hgst hq

/-- 初めて受け取った取引は、そのスロットの終わりに全員へ転送される。 -/
theorem tx_forwarded (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) {i : Fin n}
    (hi : Correct s₀ instrs i) {t : Nat} {tr : Tx}
    (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S)
    (hfirst : ∀ t' < t, Msg.tx tr ∉ ((State.run s₀ instrs t').procs i).S) (j : Fin n) :
    Action.send (Msg.tx tr) j ∈ (instrs t).actions i := by
  have hnew : Msg.tx tr ∉ (Algo.st5 f Δ lead i ((State.run s₀ instrs t).procs i)).prevS := by
    rw [Algo.st5_prevS]
    cases t with
    | zero => rw [prevS_zero hinit]; simp
    | succ t' =>
      rw [prevS_run_honest hh hi]
      intro hm
      rcases Algo.mem_S_stage_or f Δ lead i _ hm with hm | hsig
      · exact hfirst t' (Nat.lt_succ_self t') hm
      · exact absurd hsig (by simp [Msg.signer])
  have hmem : Msg.tx tr ∈ (Algo.st5 f Δ lead i ((State.run s₀ instrs t).procs i)).S :=
    Algo.S_subset_st5 f Δ lead i _ htr
  rw [hh t i (hi t)]
  exact Algo.send_mem_step_of_mem_forwardMsgs (Algo.mem_forwardMsgs_tx hmem hnew) j

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

/-- 有限個の存在は一様に押さえられる。 -/
theorem exists_bound {α : Type} {Q : Finset α} {P : α → Nat → Prop} (h : ∀ q ∈ Q, ∃ s, P q s) :
    ∃ T, ∀ q ∈ Q, ∃ s ≤ T, P q s := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨0, fun q hq => by simp at hq⟩
  | @insert a Q ha ih =>
    obtain ⟨T, hT⟩ := ih fun q hq => h q (Finset.mem_insert_of_mem hq)
    obtain ⟨s, hs⟩ := h a (Finset.mem_insert_self a Q)
    refine ⟨max T s, fun q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨s, le_max_right _ _, hs⟩
    · obtain ⟨s', hs', hP⟩ := hT q hq
      exact ⟨s', hs'.trans (le_max_left _ _), hP⟩

/-- lead(v) の提案の Tr* には、その時点で受信済みの取引がすべて入る。 -/
theorem mem_trStar_leaderBlock {f : Nat} {p : Processor n Tx} {tr : Tx} (h : Msg.tx tr ∈ p.S) :
    tr ∈ (Algo.leaderBlock f p).trStar := by
  simp only [Algo.leaderBlock, Block.trStar, List.mem_append]
  by_cases hp : tr ∈ (Algo.selectParent f p.S p.view).trStar
  · exact Or.inl hp
  · right
    simp only [Algo.payload, List.mem_filter, List.mem_filterMap, Finset.mem_toList,
      decide_eq_true_eq]
    exact ⟨⟨Msg.tx tr, h, rfl⟩, hp⟩

/-! ### 5.6 の補題 -/

/-- 正直者 r が view v 以上に達するなら、初めて達するスロット e がある。 -/
theorem entry_slot (hinit : Init s₀) {r : Fin n} {v : View} (hv : 1 ≤ v.val)
    (hreach : ∃ s, v.val ≤ (viewAt s₀ instrs r (s + 1)).val) :
    ∃ e, v.val ≤ (viewAt s₀ instrs r (e + 1)).val
      ∧ (∀ s' < e, (viewAt s₀ instrs r (s' + 1)).val < v.val)
      ∧ ((viewAt s₀ instrs r e).val < v.val ∨ (e = 0 ∧ v.val = 1)) := by
  classical
  refine ⟨Nat.find hreach, Nat.find_spec hreach,
    fun s' hs' => not_le.mp (Nat.find_min hreach hs'), ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hreach) with h0 | hpos
  · rw [h0, viewAt_zero hinit]
    rcases Nat.lt_or_ge 1 v.val with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, le_antisymm h hv⟩
  · obtain ⟨s', hs'⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    left; rw [hs']
    exact not_le.mp (Nat.find_min hreach (by rw [hs']; exact Nat.lt_succ_self s'))

/-- lead(v) が view v に入るスロット e より前に、正直者は view v のブロックに投票しない。
    e より前に投票するには lead(v) の署名付きの view v のブロックか、それへの正直者の票が
    要るから。 -/
theorem vote_slot_ge (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    {v : View} (hv : 1 ≤ v.val) (hlc : Correct s₀ instrs (lead v)) {e : Nat}
    (hemin : ∀ s' < e, (viewAt s₀ instrs (lead v) (s' + 1)).val < v.val) :
    ∀ s, ∀ r : Fin n, Correct s₀ instrs r → ∀ b : Block Tx, b.view = v → ∀ j,
      Action.send (Msg.vote r b) j ∈ (instrs s).actions r → e ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro r hr b hbv j hj
  rcases Nat.lt_or_ge s e with hlt | hge
  swap
  · exact hge
  exfalso
  have hg : b ≠ .gen := by
    intro hg; subst hg
    have : v.val = 0 := by rw [← hbv]; rfl
    omega
  have hact := hh s r (hr s)
  rw [hact] at hj
  obtain ⟨j', hj'⟩ : ∃ j', Action.send (Msg.vote r b) j'
      ∈ Algo.innerActs f Δ lead r ((State.run s₀ instrs s).procs r) := by
    rw [Algo.step_eq_stepPair, Algo.stepPair_snd'] at hj
    rcases List.mem_append.mp hj with hj | hj
    · exact ⟨j, hj⟩
    · rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.send_forwardNew_mem hj) with hm | ⟨_, j', hs'⟩
      · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hm rfl
        exact absurd (ih s' hs' r hr b hbv j'' hj'') (not_le.mpr (lt_trans hs' hlt))
      · exact ⟨j', hs'⟩
  simp only [Algo.innerActs, List.mem_append] at hj'
  rcases hj' with ((((hj' | hj') | hj') | hj') | hj')
  · -- 登り: 中間状態 q の S に b の M-notarisation。正直な投票者がそれより前に投票している
    obtain ⟨b', q, hm, _, hqv, hM, _, _, _, _, hnew, _⟩ :=
      Algo.send_climb (localInv_run hinit hh hr s) hj'
    injection hm with _ hbb
    subst hbb
    rcases hM with hg' | hM
    · exact hg hg'
    obtain ⟨w, hw, hwc⟩ := exists_correct_of_lt_card hb (lt_of_lt_of_le (by omega) hM)
    rcases hnew _ (mem_voters.mp hw) with hw' | ⟨b'', hb'', hlt'⟩
    · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hw' rfl
      exact absurd (ih s' hs' w hwc b hbv j'' hj'') (not_le.mpr (lt_trans hs' hlt))
    · injection hb'' with _ hbb
      subst hbb
      rw [hqv] at hlt'
      exact absurd hlt' (lt_irrefl _)
  · obtain ⟨_, hm⟩ := Algo.send_propose_eq hj'; cases hm
  · -- 9〜11 行: valid proposal の署名ブロックは lead(v) が送ったもの
    obtain ⟨b', hm, hbv', _, _, hvp, _⟩ := Algo.send_voteProposal_eq hj'
    injection hm with _ hbb
    subst hbb
    have hsigned := hvp.signed
    have hlv : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view = v := by
      rw [← hbv, hbv']
    rw [hlv] at hsigned
    rcases Algo.mem_S_st2 hsigned with hm2 | ⟨b'', hm2, hs2⟩
    · rcases Algo.mem_S_st1 hm2 with hm1 | ⟨_, hm1, _⟩
      · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hm1 rfl
        obtain ⟨hbb, _, _⟩ := send_block_eq hinit hh hlc hj''
        have h1 := hemin s' (lt_trans hs' hlt)
        rw [viewAt_succ_eq hh hlc s'] at h1
        have h2 : b.view = (Algo.st1 f (lead v) ((State.run s₀ instrs s').procs (lead v))).view := by
          rw [hbb]; rfl
        rw [← h2, hbv] at h1
        exact lt_irrefl _ h1
      · cases hm1
    · injection hm2 with hr' hbb
      subst hbb
      obtain ⟨hm3, _, _⟩ := Algo.send_propose_eq' hs2
      injection hm3 with _ hbb'
      subst hr'
      have h1 := hemin s hlt
      rw [viewAt_succ_eq hh hlc s] at h1
      have h2 : b.view = (Algo.st1 f (lead v) ((State.run s₀ instrs s).procs (lead v))).view := by
        rw [hbb']; rfl
      rw [← h2, hbv] at h1
      exact lt_irrefl _ h1
  · obtain ⟨hm, _⟩ := Algo.send_nullifyTimeout_eq hj'; cases hm
  · obtain ⟨hm, _⟩ := Algo.send_nullifyNoProgress_eq hj'; cases hm

/-- lead(v) が view v に入るスロット e より前に、正直者は nullify(v) を送らない。 -/
theorem nullify_slot_ge (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) (hs : PartialSync δ s₀ instrs) (hδ : δ ≤ Δ) {v : View} (hv : 1 ≤ v.val)
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hlc : Correct s₀ instrs (lead v)) {e : Nat}
    (he : e ≤ t + δ) (hemin : ∀ s' < e, (viewAt s₀ instrs (lead v) (s' + 1)).val < v.val) :
    ∀ s, ∀ r : Fin n, Correct s₀ instrs r → ∀ j,
      Action.send (Msg.nullify r v) j ∈ (instrs s).actions r → e ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro r hr j hj
  rcases Nat.lt_or_ge s e with hlt | hge
  swap
  · exact hge
  exfalso
  have hδ1 := hs.one_le
  have hact := hh s r (hr s)
  rw [hact] at hj
  obtain ⟨j', hj'⟩ : ∃ j', Action.send (Msg.nullify r v) j'
      ∈ Algo.innerActs f Δ lead r ((State.run s₀ instrs s).procs r) := by
    rw [Algo.step_eq_stepPair, Algo.stepPair_snd'] at hj
    rcases List.mem_append.mp hj with hj | hj
    · exact ⟨j, hj⟩
    · rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.send_forwardNew_mem hj) with hm | ⟨_, j', hs'⟩
      · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hm rfl
        exact absurd (ih s' hs' r hr j'' hj'') (not_le.mpr (lt_trans hs' hlt))
      · exact ⟨j', hs'⟩
  simp only [Algo.innerActs, List.mem_append] at hj'
  rcases hj' with ((((hj' | hj') | hj') | hj') | hj')
  · obtain ⟨_, _, hm, _⟩ := Algo.send_climb (localInv_run hinit hh hr s) hj'; cases hm
  · obtain ⟨_, hm⟩ := Algo.send_propose_eq hj'; cases hm
  · obtain ⟨_, hm, _⟩ := Algo.send_voteProposal_eq hj'; cases hm
  · -- 13〜14 行: r は 2Δ スロット前から view v にいるので、t ≤ s − 2Δ
    obtain ⟨hm, _, _, _, ht3⟩ := Algo.send_nullifyTimeout_eq hj'
    injection hm with _ hv3
    rw [Algo.st3_timer] at ht3
    have hst1 : Algo.st1 f r ((State.run s₀ instrs s).procs r) = (State.run s₀ instrs s).procs r := by
      rcases Algo.st1_eq_or f r ((State.run s₀ instrs s).procs r) with h | ⟨h, _⟩
      · exact h
      · rw [h] at ht3; omega
    have htimer : timerAt s₀ instrs r s = 2 * Δ := by
      show ((State.run s₀ instrs s).procs r).timer = 2 * Δ
      rw [← hst1]; exact ht3
    have hview : viewAt s₀ instrs r s = v := by
      show ((State.run s₀ instrs s).procs r).view = v
      rw [hv3, Algo.st3_view, hst1]
    have hle := timerAt_le_slot (instrs := instrs) hinit r s
    rw [htimer] at hle
    have hstay := viewAt_eq_of_lt_timer hinit r s (2 * Δ - 1) (by rw [htimer]; omega) (2 * Δ - 1)
      (le_refl _)
    rw [show s - (2 * Δ - 1) = (s - 2 * Δ) + 1 by omega, hview] at hstay
    have := hfirst.first r (s - 2 * Δ) hr (by rw [hstay])
    omega
  · -- 24〜28 行: r は view v のブロック c₀ に投票済みで、その票は e 以降
    obtain ⟨hm, _, c₀, hc₀, _⟩ := Algo.send_nullifyNoProgress_eq hj'
    injection hm with _ hv4
    have hL4 := Algo.localInv_st4 (Δ := Δ) (lead := lead) (localInv_run hinit hh hr s)
    have hvote := hL4.notar_mem c₀ hc₀
    have hcv : c₀.view = v := (hL4.notar_view c₀ hc₀).trans hv4.symm
    rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.S_st4_subset_st5 f Δ lead r _ hvote)
      with hm' | ⟨_, j'', hs''⟩
    · obtain ⟨s', hs', j₃, hj₃⟩ := sendsBefore_of_mem_S hinit hm' rfl
      exact absurd (vote_slot_ge hinit hh hb hv hlc hemin s' r hr c₀ hcv j₃ hj₃)
        (not_le.mpr (lt_trans hs' hlt))
    · have hsend : Action.send (Msg.vote r c₀) j'' ∈ (instrs s).actions r := by
        rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd']
        exact List.mem_append_left _ hs''
      exact absurd (vote_slot_ge hinit hh hb hv hlc hemin s r hr c₀ hcv j'' hsend) (not_le.mpr hlt)

/-- lead(v) が view v に入るスロット e の冒頭の S に、view v の証明書はない。 -/
theorem no_cert_at_entry (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) (hs : PartialSync δ s₀ instrs) (hδ : δ ≤ Δ) {v : View} (hv : 1 ≤ v.val)
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hlc : Correct s₀ instrs (lead v)) {e : Nat}
    (he : e ≤ t + δ) (hemin : ∀ s' < e, (viewAt s₀ instrs (lead v) (s' + 1)).val < v.val) :
    ¬ Algo.HasCert f ((State.run s₀ instrs e).procs (lead v)).S v := by
  intro hc
  rcases hc with hN | hM
  · have hcard := card_le_of_byz hb (nullifiers ((State.run s₀ instrs e).procs (lead v)).S v)
      fun q hq => exists_byz_of_not_correct fun hqc => ?_
    · unfold Nullified at hN; omega
    · obtain ⟨s', hs', j, hj⟩ := sendsBefore_of_mem_S hinit (mem_nullifiers.mp hq) rfl
      exact absurd (nullify_slot_ge hinit hh hb hs hδ hv hfirst hlc he hemin s' q hqc j hj)
        (not_le.mpr hs')
  · obtain ⟨b', hb'⟩ := List.exists_mem_of_ne_nil _ hM
    obtain ⟨hbv, hM'⟩ := Algo.mem_mNotarisedAt hb'
    rcases hM' with hg | hM'
    · subst hg
      have : v.val = 0 := by rw [← hbv]; rfl
      omega
    · have hcard := card_le_of_byz hb (voters ((State.run s₀ instrs e).procs (lead v)).S b')
        fun q hq => exists_byz_of_not_correct fun hqc => ?_
      · omega
      · obtain ⟨s', hs', j, hj⟩ := sendsBefore_of_mem_S hinit (mem_voters.mp hq) rfl
        exact absurd (vote_slot_ge hinit hh hb hv hlc hemin s' q hqc b' hbv j hj) (not_le.mpr hs')

/-- lead(v) は view v に入るスロット e に、登りを view v で終え、まだ提案していない。 -/
theorem leader_at_entry (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs)
    (hb : ByzBound f s₀ instrs) (hs : PartialSync δ s₀ instrs) (hδ : δ ≤ Δ) {v : View} (hv : 1 ≤ v.val)
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hlc : Correct s₀ instrs (lead v)) {e : Nat}
    (he : e ≤ t + δ) (hev : v.val ≤ (viewAt s₀ instrs (lead v) (e + 1)).val)
    (hemin : ∀ s' < e, (viewAt s₀ instrs (lead v) (s' + 1)).val < v.val)
    (hstart : (viewAt s₀ instrs (lead v) e).val < v.val ∨ (e = 0 ∧ v.val = 1)) :
    (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).view = v
      ∧ (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).proposed = false := by
  have hnc := no_cert_at_entry hinit hh hb hs hδ hv hfirst hlc he hemin
  rw [viewAt_succ_eq hh hlc e] at hev
  have hle : (viewAt s₀ instrs (lead v) e).val ≤ v.val := by
    rcases hstart with h | ⟨rfl, h⟩
    · exact h.le
    · rw [viewAt_zero hinit]; omega
  have hview : (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).view = v := by
    apply View.val_injective
    rcases Nat.lt_or_ge v.val (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).view.val
      with hlt | hge
    · exact absurd (Algo.st1_certs hle hlt) hnc
    · exact le_antisymm hge hev
  refine ⟨hview, ?_⟩
  rcases Algo.st1_eq_or f (lead v) ((State.run s₀ instrs e).procs (lead v)) with h | ⟨_, h⟩
  · rw [h]
    rcases hstart with hlt | ⟨rfl, _⟩
    · exfalso
      rw [h] at hview
      have : (viewAt s₀ instrs (lead v) e).val = v.val := congrArg View.val hview
      omega
    · show ((State.run s₀ instrs 0).procs (lead v)).proposed = false
      rw [State.run, hinit.procs]; rfl
  · exact h

/-- Lemma 5.6 の設定: view v ≥ 1 の lead(v) は正直で、最初の正直者が t ≥ GST に view v に入り、
    lead(v) 自身は t ≤ e ≤ t + δ のスロット e に初めて view v 以上になる。δ ≤ Δ は GST 後の
    実際の遅延の上界。 -/
structure LeaderRound (f Δ δ : Nat) (lead : View → Fin n) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) (hs : PartialSync δ s₀ instrs) (v : View) (t e : Nat) : Prop where
  hδ : δ ≤ Δ
  hv : 1 ≤ v.val
  hfirst : FirstEntry s₀ instrs v t
  hgst : hs.GST.val ≤ t
  hlc : Correct s₀ instrs (lead v)
  he : e ≤ t + δ
  hev : v.val ≤ (viewAt s₀ instrs (lead v) (e + 1)).val
  hemin : ∀ s' < e, (viewAt s₀ instrs (lead v) (s' + 1)).val < v.val
  hstart : (viewAt s₀ instrs (lead v) e).val < v.val ∨ (e = 0 ∧ v.val = 1)

/-- lead(v) がスロット e に提案するブロック。 -/
noncomputable def leaderBlockAt (f : Nat) (lead : View → Fin n) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) (v : View) (e : Nat) : Block Tx :=
  Algo.leaderBlock f (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v)))

/-- その親。 -/
noncomputable def leaderParentAt (f : Nat) (lead : View → Fin n) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) (v : View) (e : Nat) : Block Tx :=
  Algo.selectParent f (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).S
    (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).view

theorem leaderBlockAt_parent (f : Nat) (lead : View → Fin n) (s₀ : State n Tx)
    (instrs : Nat → Instr n Tx) (v : View) (e : Nat) :
    (leaderBlockAt f lead s₀ instrs v e).parent = some (leaderParentAt f lead s₀ instrs v e) := rfl

section CorrectLeader

variable (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
  (hs : PartialSync δ s₀ instrs) {v : View} {t e : Nat} (R : LeaderRound f Δ δ lead s₀ instrs hs v t e)

include hinit hh hb hs R

theorem leaderBlockAt_view : (leaderBlockAt f lead s₀ instrs v e).view = v :=
  (leader_at_entry hinit hh hb hs R.hδ R.hv R.hfirst R.hlc R.he R.hev R.hemin R.hstart).1

theorem leaderParentAt_view_lt : (leaderParentAt f lead s₀ instrs v e).view.val < v.val := by
  have hview := (leader_at_entry hinit hh hb hs R.hδ R.hv R.hfirst R.hlc R.he R.hev R.hemin R.hstart).1
  unfold leaderParentAt
  rw [hview]
  exact Algo.selectParent_view_lt f _ R.hv

/-- lead(v) はスロット e にブロックを全員へ送る。 -/
theorem leader_proposes (j : Fin n) :
    Action.send (Msg.block (lead v) (leaderBlockAt f lead s₀ instrs v e)) j
      ∈ (instrs e).actions (lead v) := by
  obtain ⟨hview, hprop⟩ :=
    leader_at_entry hinit hh hb hs R.hδ R.hv R.hfirst R.hlc R.he R.hev R.hemin R.hstart
  rw [hh e (lead v) (R.hlc e), Algo.step_eq_stepPair, Algo.stepPair_snd']
  apply List.mem_append_left
  simp only [Algo.innerActs, List.mem_append]
  left; left; left; right
  exact Algo.propose_fires (by rw [hview]) hprop j

theorem t_le_e : t ≤ e := R.hfirst.first (lead v) e R.hlc R.hev

/-- ブロックは t + 2Δ までに全正直者に届く。 -/
theorem leader_block_delivered {r : Fin n} {T : Nat} (hT : t + 2 * δ ≤ T) :
    Msg.block (lead v) (leaderBlockAt f lead s₀ instrs v e) ∈ ((State.run s₀ instrs T).procs r).S := by
  have hδ1 := hs.one_le
  have hδ := R.hδ
  have he := R.he
  have hgst := R.hgst
  exact delivered hinit hh hs R.hlc (leader_proposes hinit hh hb hs R r) (by omega) (by omega)

/-- 親の M-notarisation は t + 2Δ までに全正直者に届く。 -/
theorem leader_parent_mnotarised_all {r : Fin n} {T : Nat} (hT : t + 2 * δ ≤ T) :
    MNotarised f ((State.run s₀ instrs T).procs r).S (leaderParentAt f lead s₀ instrs v e) := by
  have hδ1 := hs.one_le
  have hδ := R.hδ
  have he := R.he
  have hgst := R.hgst
  have h1 : MNotarised f (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).S
      (leaderParentAt f lead s₀ instrs v e) := Algo.selectParent_mnotarised f _ _
  have h5 := h1.mono (Algo.S_st1_subset_st5 f Δ lead (lead v) _)
  exact mnotarised_all_end hinit hh hs R.hlc h5 (by omega) (by omega)

/-- 親の view と v の間の view の nullification は t + 2Δ までに全正直者に届く。 -/
theorem leader_gaps_nullified_all {r : Fin n} (hr : Correct s₀ instrs r) {T : Nat}
    (hT : t + 2 * δ ≤ T) {w : View}
    (h1 : (leaderParentAt f lead s₀ instrs v e).view.val < w.val) (h2 : w.val < v.val) :
    Nullified f ((State.run s₀ instrs T).procs r).S w := by
  have hδ1 := hs.one_le
  have hδ := R.hδ
  have he := R.he
  have hgst := R.hgst
  have hview := (leader_at_entry hinit hh hb hs R.hδ R.hv R.hfirst R.hlc R.he R.hev R.hemin R.hstart).1
  have hw1 : 1 ≤ w.val := by omega
  obtain ⟨s', hs'_lt, hs1, hs2⟩ := exists_leave_slot hinit hw1 (lt_of_lt_of_le h2 R.hev)
  have hcert : Algo.HasCert f ((State.run s₀ instrs s').procs (lead v)).S w := by
    rw [viewAt_succ_eq hh R.hlc s'] at hs2
    exact Algo.st1_certs hs1 hs2
  rcases hcert with hN | hM
  · exact nullified_all hinit hh hs R.hlc hr hN (by omega) (by omega)
  · exfalso
    obtain ⟨b'', hb''⟩ := List.exists_mem_of_ne_nil _ hM
    obtain ⟨hbv, hM''⟩ := Algo.mem_mNotarisedAt hb''
    have hsub : ((State.run s₀ instrs s').procs (lead v)).S
        ⊆ (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).S :=
      (S_subset_run s₀ instrs (lead v) (Nat.lt_succ_iff.mp hs'_lt)).trans
        (Algo.S_subset_st1 f (lead v) _)
    obtain ⟨q, hq⟩ := Algo.exists_vote_of_mem_votedBlocks (Algo.mem_votedBlocks_of_mem_mNotarisedAt hb'')
    have hmax := Algo.selectParent_max f
      (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).S
      (Algo.st1 f (lead v) ((State.run s₀ instrs e).procs (lead v))).view
      (Algo.mem_votedBlocks (hsub hq)) (by rw [hbv, hview]; exact h2) (hM''.mono hsub)
    rw [hbv] at hmax
    exact absurd h1 (not_lt.mpr hmax)

/-- t + 2Δ 以降、全正直者の S でブロックは valid proposal。 -/
theorem leader_valid_at {r : Fin n} (hr : Correct s₀ instrs r) {T : Nat} (hT : t + 2 * δ ≤ T) :
    ValidProposal f lead ((State.run s₀ instrs T).procs r).S v (leaderBlockAt f lead s₀ instrs v e) := by
  refine ⟨leaderBlockAt_view hinit hh hb hs R, leader_block_delivered hinit hh hb hs R hT, ?_,
    Algo.leaderBlock_ne_gen _ _, ?_, ?_⟩
  · intro b' hb'v hb'
    obtain ⟨s', _, j, hj⟩ := sendsBefore_of_mem_S hinit hb' rfl
    exact leader_block_unique hinit hh R.hlc hj (leader_proposes hinit hh hb hs R r)
      (by rw [hb'v, leaderBlockAt_view hinit hh hb hs R])
  · intro p₀ hp₀
    rw [leaderBlockAt_parent] at hp₀
    obtain rfl := Option.some.inj (Option.mem_def.mp hp₀).symm
    exact leader_parent_mnotarised_all hinit hh hb hs R hT
  · intro p₀ hp₀ w h1 h2
    rw [leaderBlockAt_parent] at hp₀
    obtain rfl := Option.some.inj (Option.mem_def.mp hp₀).symm
    exact leader_gaps_nullified_all hinit hh hb hs R hr hT h1 h2

/-- 正直者の view v のブロックへの票は、すべて lead(v) のブロックへの票。 -/
theorem vote_unique_leaderBlock :
    ∀ s, ∀ r : Fin n, Correct s₀ instrs r → ∀ b : Block Tx, b.view = v → ∀ j,
      Action.send (Msg.vote r b) j ∈ (instrs s).actions r →
      b = leaderBlockAt f lead s₀ instrs v e := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro r hr b hbv j hj
  have hv := R.hv
  have hg : b ≠ .gen := by
    intro hg; subst hg
    have : v.val = 0 := by rw [← hbv]; rfl
    omega
  have hact := hh s r (hr s)
  have hinner : ∀ j', Action.send (Msg.vote r b) j'
      ∈ Algo.innerActs f Δ lead r ((State.run s₀ instrs s).procs r) →
      b = leaderBlockAt f lead s₀ instrs v e := by
    intro j' hj'
    simp only [Algo.innerActs, List.mem_append] at hj'
    rcases hj' with ((((hj' | hj') | hj') | hj') | hj')
    · obtain ⟨b', q, hm, _, hqv, hM, _, _, _, _, hnew, _⟩ :=
        Algo.send_climb (localInv_run hinit hh hr s) hj'
      injection hm with _ hbb
      subst hbb
      rcases hM with hg' | hM
      · exact absurd hg' hg
      obtain ⟨w, hw, hwc⟩ := exists_correct_of_lt_card hb (lt_of_lt_of_le (by omega) hM)
      rcases hnew _ (mem_voters.mp hw) with hw' | ⟨b'', hb'', hlt'⟩
      · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hw' rfl
        exact ih s' hs' w hwc b hbv j'' hj''
      · injection hb'' with _ hbb
        subst hbb
        rw [hqv] at hlt'
        exact absurd hlt' (lt_irrefl _)
    · obtain ⟨_, hm⟩ := Algo.send_propose_eq hj'; cases hm
    · obtain ⟨b', hm, hbv', _, _, hvp, _⟩ := Algo.send_voteProposal_eq hj'
      injection hm with _ hbb
      subst hbb
      have hsigned := hvp.signed
      have hlv : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view = v := by
        rw [← hbv, hbv']
      rw [hlv] at hsigned
      rcases Algo.mem_S_st2 hsigned with hm2 | ⟨b'', hm2, hs2⟩
      · rcases Algo.mem_S_st1 hm2 with hm1 | ⟨_, hm1, _⟩
        · obtain ⟨s', _, j'', hj''⟩ := sendsBefore_of_mem_S hinit hm1 rfl
          exact leader_block_unique hinit hh R.hlc hj'' (leader_proposes hinit hh hb hs R r)
            (by rw [hbv, leaderBlockAt_view hinit hh hb hs R])
        · cases hm1
      · injection hm2 with hr' hbb
        subst hbb
        subst hr'
        have hsend : Action.send (Msg.block (lead v) b) (lead v) ∈ (instrs s).actions (lead v) := by
          rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd']
          apply List.mem_append_left
          simp only [Algo.innerActs, List.mem_append]
          left; left; left; right
          exact hs2
        exact leader_block_unique hinit hh R.hlc hsend (leader_proposes hinit hh hb hs R (lead v))
          (by rw [hbv, leaderBlockAt_view hinit hh hb hs R])
    · obtain ⟨hm, _⟩ := Algo.send_nullifyTimeout_eq hj'; cases hm
    · obtain ⟨hm, _⟩ := Algo.send_nullifyNoProgress_eq hj'; cases hm
  rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd'] at hj
  rcases List.mem_append.mp hj with hj | hj
  · exact hinner j hj
  · rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.send_forwardNew_mem hj) with hm | ⟨_, j', hs'⟩
    · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hm rfl
      exact ih s' hs' r hr b hbv j'' hj''
    · exact hinner j' hs'

/-- 正直者は timeout で nullify(v) を送らない: timeout の時点で lead(v) のブロックは valid
    proposal として届いていて、9〜11 行が先に投票するから。 -/
theorem no_timeout_nullify :
    ∀ s, ∀ r : Fin n, Correct s₀ instrs r → ∀ j,
      Action.send (Msg.nullify r v) j
        ∈ (Algo.nullifyTimeout Δ r (Algo.st3 f lead r ((State.run s₀ instrs s).procs r))).2 →
      False := by
  intro s r hr j hj
  have hδ1 := hs.one_le
  have hδ := R.hδ
  have hv := R.hv
  obtain ⟨hm, hnl3, hnot3, _, ht3⟩ := Algo.send_nullifyTimeout_eq hj
  injection hm with _ hv3
  rw [Algo.st3_timer] at ht3
  have hst1 : Algo.st1 f r ((State.run s₀ instrs s).procs r) = (State.run s₀ instrs s).procs r := by
    rcases Algo.st1_eq_or f r ((State.run s₀ instrs s).procs r) with h | ⟨h, _⟩
    · exact h
    · rw [h] at ht3; omega
  have htimer : timerAt s₀ instrs r s = 2 * Δ := by
    show ((State.run s₀ instrs s).procs r).timer = 2 * Δ
    rw [← hst1]; exact ht3
  have hview : viewAt s₀ instrs r s = v := by
    show ((State.run s₀ instrs s).procs r).view = v
    rw [hv3, Algo.st3_view, hst1]
  -- t + 2Δ ≤ s
  have hle := timerAt_le_slot (instrs := instrs) hinit r s
  rw [htimer] at hle
  have hstay := viewAt_eq_of_lt_timer hinit r s (2 * Δ - 1) (by rw [htimer]; omega) (2 * Δ - 1)
    (le_refl _)
  rw [show s - (2 * Δ - 1) = (s - 2 * Δ) + 1 by omega, hview] at hstay
  have hT : t + 2 * Δ ≤ s := by
    have := R.hfirst.first r (s - 2 * Δ) hr (by rw [hstay])
    omega
  -- lead(v) のブロックは S にあり valid
  have hvalid := leader_valid_at hinit hh hb hs R hr (T := s) (by omega)
  have hst2S : ((State.run s₀ instrs s).procs r).S
      ⊆ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S :=
    Algo.S_subset_st2 f lead r _
  have hst2v : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view = v := by
    rw [Algo.st2_view, hst1]; exact hview
  have hbLv := leaderBlockAt_view hinit hh hb hs R
  have huniq : ∀ b', b'.view = (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view →
      Msg.block (lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view) b'
        ∈ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S →
      b' = leaderBlockAt f lead s₀ instrs v e := by
    intro b' hb'v hb'
    rw [hst2v] at hb'v hb'
    rcases Algo.mem_S_st2 hb' with hm2 | ⟨b'', hm2, hs2⟩
    · rw [hst1] at hm2
      exact hvalid.unique b' hb'v hm2
    · injection hm2 with hr' _
      obtain ⟨_, _, hp⟩ := Algo.send_propose_eq' hs2
      subst hr'
      have hP : Algo.PropInv (lead v) (Algo.st1 f (lead v) ((State.run s₀ instrs s).procs (lead v))) :=
        (propInv_run hinit hh hr s).climb (f := f) _
      have hmem : Msg.block (lead v) (leaderBlockAt f lead s₀ instrs v e)
          ∈ (Algo.st1 f (lead v) ((State.run s₀ instrs s).procs (lead v))).S :=
        Algo.S_subset_st1 f (lead v) _ (leader_block_delivered hinit hh hb hs R (by omega))
      have hflag := hP.prop_flag _ hmem (by rw [hst1]; exact hbLv.trans hview.symm)
      rw [hp] at hflag; cases hflag
  have hvp2 : ValidProposal f lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S
      (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view (leaderBlockAt f lead s₀ instrs v e) :=
    ⟨by rw [hst2v]; exact hbLv, by rw [hst2v]; exact hst2S hvalid.signed, huniq,
      Algo.leaderBlock_ne_gen _ _, fun p₀ hp₀ => (hvalid.parent p₀ hp₀).mono hst2S,
      fun p₀ hp₀ w h1 h2 => (hvalid.gaps p₀ hp₀ w h1 (by rw [hst2v] at h2; exact h2)).mono hst2S⟩
  have hprop : Algo.proposals lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S
      (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view = [leaderBlockAt f lead s₀ instrs v e] :=
    Algo.proposals_eq_singleton (by rw [hst2v]; exact hst2S hvalid.signed) (by rw [hst2v]; exact hbLv)
      huniq
  have h3 := Algo.voteProposal_eq_of_singleton (f := f) (i := r) hprop
  have hnot3' : (Algo.voteProposal f lead r (Algo.st2 f lead r ((State.run s₀ instrs s).procs r))).1.notarised
      = none := hnot3
  have hnl3' : (Algo.voteProposal f lead r (Algo.st2 f lead r ((State.run s₀ instrs s).procs r))).1.nullified
      = false := hnl3
  rw [h3] at hnot3' hnl3'
  split_ifs at hnot3' hnl3' with hcond
  · rw [Algo.disseminate_vote_notarised (by rw [hst2v]; exact hbLv)] at hnot3'
    cases hnot3'
  · exact hcond ⟨hvp2, hnot3', hnl3'⟩

/-- 正直者は nullify(v) を送らない。 -/
theorem no_nullify_v :
    ∀ s, ∀ r : Fin n, Correct s₀ instrs r → ∀ j,
      Action.send (Msg.nullify r v) j ∈ (instrs s).actions r → False := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro r hr j hj
  have hact := hh s r (hr s)
  have hinner : ∀ j', Action.send (Msg.nullify r v) j'
      ∈ Algo.innerActs f Δ lead r ((State.run s₀ instrs s).procs r) → False := by
    intro j' hj'
    simp only [Algo.innerActs, List.mem_append] at hj'
    rcases hj' with ((((hj' | hj') | hj') | hj') | hj')
    · obtain ⟨_, _, hm, _⟩ := Algo.send_climb (localInv_run hinit hh hr s) hj'; cases hm
    · obtain ⟨_, hm⟩ := Algo.send_propose_eq hj'; cases hm
    · obtain ⟨_, hm, _⟩ := Algo.send_voteProposal_eq hj'; cases hm
    · exact no_timeout_nullify hinit hh hb hs R s r hr j' hj'
    · -- 24〜28 行: 証拠の署名者に正直者はいない
      obtain ⟨hm, _, c₀, hc₀, hnp⟩ := Algo.send_nullifyNoProgress_eq hj'
      injection hm with _ hv4
      have hL4 := Algo.localInv_st4 (Δ := Δ) (lead := lead) (localInv_run hinit hh hr s)
      have hvote := hL4.notar_mem c₀ hc₀
      have hcv : c₀.view = v := (hL4.notar_view c₀ hc₀).trans hv4.symm
      -- c₀ は lead(v) のブロック
      have hc₀eq : c₀ = leaderBlockAt f lead s₀ instrs v e := by
        rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.S_st4_subset_st5 f Δ lead r _ hvote)
          with hm' | ⟨_, j'', hs''⟩
        · obtain ⟨s', _, j₃, hj₃⟩ := sendsBefore_of_mem_S hinit hm' rfl
          exact vote_unique_leaderBlock hinit hh hb hs R s' r hr c₀ hcv j₃ hj₃
        · have hsend : Action.send (Msg.vote r c₀) j'' ∈ (instrs s).actions r := by
            rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd']
            exact List.mem_append_left _ hs''
          exact vote_unique_leaderBlock hinit hh hb hs R s r hr c₀ hcv j'' hsend
      rw [← hv4] at hnp
      obtain ⟨w, hw, hwc⟩ := exists_correct_of_lt_card hb (lt_of_lt_of_le (by omega) hnp)
      rcases mem_noProgressWitnesses.mp hw with hwn | ⟨b'', hb''v, hne, hwv⟩
      · -- 正直者 w の nullify(v)
        by_cases hwr : w = r
        · subst hwr
          rcases Algo.mem_S_st4_nullify hwn with hm' | hs''
          · obtain ⟨s', hs', j₃, hj₃⟩ := sendsBefore_of_mem_S hinit hm' rfl
            exact ih s' hs' w hwc j₃ hj₃
          · exact no_timeout_nullify hinit hh hb hs R s w hwc w hs''
        · have hm' : Msg.nullify w v ∈ ((State.run s₀ instrs s).procs r).S := by
            rcases Algo.mem_S_stage_or f Δ lead r _ (Algo.S_st4_subset_st5 f Δ lead r _ hwn)
              with hm' | hsig
            · exact hm'
            · simp only [Msg.signer, Option.some.injEq] at hsig
              exact absurd hsig hwr
          obtain ⟨s', hs', j₃, hj₃⟩ := sendsBefore_of_mem_S hinit hm' rfl
          exact ih s' hs' w hwc j₃ hj₃
      · -- 正直者 w の、lead(v) のブロック以外への票はない
        have hb''eq : b'' = leaderBlockAt f lead s₀ instrs v e := by
          rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.S_st4_subset_st5 f Δ lead r _ hwv)
            with hm' | ⟨hsig, j'', hs''⟩
          · obtain ⟨s', _, j₃, hj₃⟩ := sendsBefore_of_mem_S hinit hm' rfl
            exact vote_unique_leaderBlock hinit hh hb hs R s' w hwc b'' hb''v j₃ hj₃
          · simp only [Msg.signer, Option.some.injEq] at hsig
            subst hsig
            have hsend : Action.send (Msg.vote w b'') j'' ∈ (instrs s).actions w := by
              rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd']
              exact List.mem_append_left _ hs''
            exact vote_unique_leaderBlock hinit hh hb hs R s w hwc b'' hb''v j'' hsend
        exact hne (by rw [hb''eq, hc₀eq])
  rw [hact, Algo.step_eq_stepPair, Algo.stepPair_snd'] at hj
  rcases List.mem_append.mp hj with hj | hj
  · exact hinner j hj
  · rcases Algo.mem_S_stage_or_sent f Δ lead r _ (Algo.send_forwardNew_mem hj) with hm | ⟨_, j', hs'⟩
    · obtain ⟨s', hs', j'', hj''⟩ := sendsBefore_of_mem_S hinit hm rfl
      exact ih s' hs' r hr j'' hj''
    · exact hinner j' hs'

/-- 正直者 r が view v を通過するスロット s では、そのとき lead(v) のブロックに投票するか、
    既に投票している。 -/
theorem vote_at_pass {r : Fin n} (hr : Correct s₀ instrs r) {s : Nat}
    (hs1 : (viewAt s₀ instrs r s).val ≤ v.val) (hs2 : v.val < (viewAt s₀ instrs r (s + 1)).val) :
    ∃ s' ≤ s, ∃ j, Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v e)) j
      ∈ (instrs s').actions r := by
  rw [viewAt_succ_eq hh hr s] at hs2
  obtain ⟨q, hLq, hqv, _, hcert, hnew, hqS, hqsend⟩ :=
    Algo.climb_pass (localInv_run hinit hh hr s) hs1 hs2
  have hqsucc : q.S ⊆ ((State.run s₀ instrs (s + 1)).procs r).S :=
    (Algo.S_subset_advanceOnce f r q).trans
      (hqS.trans ((Algo.S_st1_subset_st5 f Δ lead r _).trans (S_st5_subset_succ hh hr s)))
  have hN : ¬ Nullified f q.S v := by
    intro hN
    have hcard := card_le_of_byz hb (nullifiers q.S v)
      fun w hw => exists_byz_of_not_correct fun hwc => ?_
    · unfold Nullified at hN; omega
    · rcases hnew _ (mem_nullifiers.mp hw) with hm | ⟨_, hm, _⟩
      · obtain ⟨s', _, j, hj⟩ := sendsBefore_of_mem_S hinit hm rfl
        exact no_nullify_v hinit hh hb hs R s' w hwc j hj
      · cases hm
  have hM : Algo.mNotarisedAt f q.S q.view ≠ [] := by
    rw [hqv]; exact hcert.resolve_left hN
  rcases hnot : q.notarised with _ | c
  · rcases hnl : q.nullified with _ | _
    · obtain ⟨b'', hb'', hsend⟩ := Algo.advanceOnce_vote_of r (by rw [hqv]; exact hN) hM hnot hnl
      have hsend' : Action.send (Msg.vote r b'') r ∈ (instrs s).actions r := by
        rw [hh s r (hr s), Algo.step_eq_stepPair, Algo.stepPair_snd']
        apply List.mem_append_left
        simp only [Algo.innerActs, List.mem_append]
        left; left; left; left
        exact hqsend _ _ hsend
      have hbv := (Algo.mem_mNotarisedAt hb'').1
      rw [hqv] at hbv
      have := vote_unique_leaderBlock hinit hh hb hs R s r hr b'' hbv r hsend'
      refine ⟨s, le_refl _, r, ?_⟩
      rw [← this]; exact hsend'
    · have hmem := hLq.null_mem hnl
      rw [hqv] at hmem
      obtain ⟨s', _, j, hj⟩ := sendsBefore_of_mem_S hinit (hqsucc hmem) rfl
      exact absurd hj (no_nullify_v hinit hh hb hs R s' r hr j)
  · have hcv := (hLq.notar_view c hnot).trans hqv
    obtain ⟨s', hs', j, hj⟩ := sendsBefore_of_mem_S hinit (hqsucc (hLq.notar_mem c hnot)) rfl
    have := vote_unique_leaderBlock hinit hh hb hs R s' r hr c hcv j hj
    refine ⟨s', Nat.lt_succ_iff.mp hs', j, ?_⟩
    rw [← this]; exact hj

/-- t + 2δ 以降に登りを view v で終える正直者は、そのスロットで 9〜11 行により投票するか、
    既に投票している。 -/
theorem vote_line11 {r : Fin n} (hr : Correct s₀ instrs r) {s : Nat} (hT : t + 2 * δ ≤ s)
    (hst1v : (Algo.st1 f r ((State.run s₀ instrs s).procs r)).view = v) :
    ∃ s' ≤ s, ∃ j, Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v e)) j
      ∈ (instrs s').actions r := by
  have hvalid := leader_valid_at hinit hh hb hs R hr (T := s) hT
  have hbLv := leaderBlockAt_view hinit hh hb hs R
  have hst1S : ((State.run s₀ instrs s).procs r).S
      ⊆ (Algo.st1 f r ((State.run s₀ instrs s).procs r)).S := Algo.S_subset_st1 f r _
  have hst2S : (Algo.st1 f r ((State.run s₀ instrs s).procs r)).S
      ⊆ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S := Algo.S_subset_propose f lead r _
  have hst2v : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view = v := by
    rw [Algo.st2_view, hst1v]
  have hL1 := Algo.localInv_st1 (localInv_run hinit hh hr s)
  have hclimb_send : ∀ m j, Action.send m j
      ∈ (Algo.climb f r (Algo.maxView ((State.run s₀ instrs s).procs r).S + 1)
          ((State.run s₀ instrs s).procs r)).2 →
      Action.send m j ∈ (instrs s).actions r := by
    intro m j hm
    rw [hh s r (hr s), Algo.step_eq_stepPair, Algo.stepPair_snd']
    apply List.mem_append_left
    simp only [Algo.innerActs, List.mem_append]
    left; left; left; left
    exact hm
  have huniq : ∀ b', b'.view = (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view →
      Msg.block (lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view) b'
        ∈ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S →
      b' = leaderBlockAt f lead s₀ instrs v e := by
    intro b' hb'v hb'
    rw [hst2v] at hb'v hb'
    rcases Algo.mem_S_st2 hb' with hm2 | ⟨b'', hm2, hs2⟩
    · rcases Algo.mem_S_st1 hm2 with hm1 | ⟨_, hm1, _⟩
      · exact hvalid.unique b' hb'v hm1
      · cases hm1
    · injection hm2 with hr' _
      obtain ⟨_, _, hp⟩ := Algo.send_propose_eq' hs2
      subst hr'
      have hP : Algo.PropInv (lead v) (Algo.st1 f (lead v) ((State.run s₀ instrs s).procs (lead v))) :=
        (propInv_run hinit hh hr s).climb (f := f) _
      have hmem : Msg.block (lead v) (leaderBlockAt f lead s₀ instrs v e)
          ∈ (Algo.st1 f (lead v) ((State.run s₀ instrs s).procs (lead v))).S :=
        hst1S (leader_block_delivered hinit hh hb hs R hT)
      have hflag := hP.prop_flag _ hmem (hbLv.trans hst1v.symm)
      rw [hp] at hflag; cases hflag
  have hvp2 : ValidProposal f lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S
      (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view (leaderBlockAt f lead s₀ instrs v e) :=
    ⟨by rw [hst2v]; exact hbLv, by rw [hst2v]; exact hst2S (hst1S hvalid.signed), huniq,
      Algo.leaderBlock_ne_gen _ _, fun p₀ hp₀ => (hvalid.parent p₀ hp₀).mono (hst1S.trans hst2S),
      fun p₀ hp₀ w h1 h2 =>
        (hvalid.gaps p₀ hp₀ w h1 (by rw [hst2v] at h2; exact h2)).mono (hst1S.trans hst2S)⟩
  have hprop : Algo.proposals lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S
      (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view = [leaderBlockAt f lead s₀ instrs v e] :=
    Algo.proposals_eq_singleton (by rw [hst2v]; exact hst2S (hst1S hvalid.signed))
      (by rw [hst2v]; exact hbLv) huniq
  have h3 := Algo.voteProposal_eq_of_singleton (f := f) (i := r) hprop
  by_cases hcond : ValidProposal f lead (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).S
      (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).view (leaderBlockAt f lead s₀ instrs v e)
      ∧ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).notarised = none
      ∧ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).nullified = false
  · refine ⟨s, le_refl _, r, ?_⟩
    rw [hh s r (hr s), Algo.step_eq_stepPair, Algo.stepPair_snd']
    apply List.mem_append_left
    simp only [Algo.innerActs, List.mem_append]
    left; left; right
    rw [h3, if_pos hcond]
    exact Algo.mem_disseminate_snd.mpr ⟨r, rfl⟩
  · have hnn : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).notarised ≠ none
        ∨ (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).nullified = true := by
      by_cases h1 : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).notarised = none
      · by_cases h2 : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).nullified = false
        · exact absurd ⟨hvp2, h1, h2⟩ hcond
        · right; simpa using h2
      · exact Or.inl h1
    have hn2 : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).notarised
        = (Algo.st1 f r ((State.run s₀ instrs s).procs r)).notarised := Algo.propose_notarised f lead r _
    have hl2 : (Algo.st2 f lead r ((State.run s₀ instrs s).procs r)).nullified
        = (Algo.st1 f r ((State.run s₀ instrs s).procs r)).nullified := Algo.propose_nullified f lead r _
    rcases hnn with hnot | hnl
    · rw [hn2] at hnot
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hnot
      have hcv : c.view = v := (hL1.notar_view c hc).trans hst1v
      rcases Algo.mem_S_st1 (hL1.notar_mem c hc) with hm1 | ⟨b', hb', _, j, hj⟩
      · obtain ⟨s', hs', j, hj⟩ := sendsBefore_of_mem_S hinit hm1 rfl
        have := vote_unique_leaderBlock hinit hh hb hs R s' r hr c hcv j hj
        refine ⟨s', hs'.le, j, ?_⟩
        rw [← this]; exact hj
      · injection hb' with _ hbb
        subst hbb
        have hj' := hclimb_send _ _ hj
        have := vote_unique_leaderBlock hinit hh hb hs R s r hr c hcv j hj'
        refine ⟨s, le_refl _, j, ?_⟩
        rw [← this]; exact hj'
    · rw [hl2] at hnl
      have hmem := hL1.null_mem hnl
      rw [hst1v] at hmem
      rcases Algo.mem_S_st1 hmem with hm1 | ⟨_, hb', _⟩
      · obtain ⟨s', _, j, hj⟩ := sendsBefore_of_mem_S hinit hm1 rfl
        exact absurd hj (no_nullify_v hinit hh hb hs R s' r hr j)
      · cases hb'

/-- t + 2δ 以降のスロット s の終わりに view v 以上にいる正直者は、s までに lead(v) の
    ブロックに投票している。 -/
theorem vote_by {r : Fin n} (hr : Correct s₀ instrs r) {s : Nat} (hT : t + 2 * δ ≤ s)
    (hle : v.val ≤ (viewAt s₀ instrs r (s + 1)).val) :
    ∃ s' ≤ s, ∃ j, Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v e)) j
      ∈ (instrs s').actions r := by
  rcases Nat.lt_or_ge v.val (viewAt s₀ instrs r (s + 1)).val with hlt | hge
  · rcases Nat.lt_or_ge v.val (viewAt s₀ instrs r s).val with hlt' | hge'
    · obtain ⟨s'', hs'', h1, h2⟩ := exists_leave_slot hinit R.hv hlt'
      obtain ⟨s', hs', j, hj⟩ := vote_at_pass hinit hh hb hs R hr h1 h2
      exact ⟨s', by omega, j, hj⟩
    · exact vote_at_pass hinit hh hb hs R hr hge' hlt
  · have heq : (viewAt s₀ instrs r (s + 1)).val = v.val := le_antisymm hge hle
    have hst1v : (Algo.st1 f r ((State.run s₀ instrs s).procs r)).view = v := by
      rw [← viewAt_succ_eq hh hr s]; exact View.val_injective heq
    exact vote_line11 hinit hh hb hs R hr hT hst1v

/-- 全正直者が lead(v) のブロックに投票する。 -/
theorem all_vote_leaderBlock (hn : 5 * f + 1 ≤ n) {r : Fin n} (hr : Correct s₀ instrs r) :
    Sends instrs r (Msg.vote r (leaderBlockAt f lead s₀ instrs v e)) := by
  obtain ⟨T, hT⟩ := progression hn hinit hh hb (hs.mono R.hδ) hr ⟨v.val + 1⟩
  obtain ⟨s, _, hs1, hs2⟩ := exists_leave_slot hinit R.hv (Nat.lt_of_succ_le hT)
  obtain ⟨s', _, j, hj⟩ := vote_at_pass hinit hh hb hs R hr hs1 hs2
  exact ⟨s', j, hj⟩

end CorrectLeader

/-- Lemma 5.6 の設定は、lead(v) が正直で最初の正直者が GST 以降に v に入れば作れる。 -/
theorem leader_round (hinit : Init s₀) (hh : Honest f Δ lead s₀ instrs) (hs : PartialSync δ s₀ instrs)
    (hδ : δ ≤ Δ) {v : View} (hv : 1 ≤ v.val) (hi : Correct s₀ instrs (lead v)) {t : Nat}
    (hfirst : FirstEntry s₀ instrs v t) (hgst : hs.GST.val ≤ t) :
    ∃ e, LeaderRound f Δ δ lead s₀ instrs hs v t e := by
  have hreach : ∃ s, v.val ≤ (viewAt s₀ instrs (lead v) (s + 1)).val :=
    ⟨t + δ, enter_all hinit hh hs hfirst hgst hi⟩
  obtain ⟨e, hev, hemin, hstart⟩ := entry_slot hinit hv hreach
  have he : e ≤ t + δ := by
    rcases Nat.lt_or_ge (t + δ) e with h | h
    · exact absurd (enter_all hinit hh hs hfirst hgst hi) (not_le.mpr (hemin (t + δ) h))
    · exact h
  exact ⟨e, ⟨hδ, hv, hfirst, hgst, hi, he, hev, hemin, hstart⟩⟩

/-- Lemma 5.6（Correct leaders finalise blocks）: lead(v) が正直で、最初の正直者が GST 以降に
    view v に入るなら、lead(v) はブロックを送り、それは L-notarisation を受ける。 -/
theorem correct_leader_finalises (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hs : PartialSync Δ s₀ instrs) {v : View} (hv : 1 ≤ v.val) (hi : Correct s₀ instrs (lead v))
    {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : hs.GST.val ≤ t) :
    ∃ b : Block Tx, b.view = v ∧ Sends instrs (lead v) (.block (lead v) b)
      ∧ ReceivesL f instrs b := by
  obtain ⟨e, R⟩ := leader_round hinit hh hs (le_refl Δ) hv hi hfirst hgst
  refine ⟨leaderBlockAt f lead s₀ instrs v e, leaderBlockAt_view hinit hh hb hs R,
    ⟨e, lead v, leader_proposes hinit hh hb hs R (lead v)⟩, ?_⟩
  right
  refine (card_correctSet hb).trans (Finset.card_le_card fun r hr => ?_)
  exact mem_voteSenders.mpr (all_vote_leaderBlock hinit hh hb hs R hn (mem_correctSet.mp hr))

/-- Lemma 5.7（Liveness）: 正直者 p_i が受け取った取引は、正直者 p_j が L-notarisation を
    持つブロックの Tr* にいつか入る。 -/
theorem liveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
    (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
    (hs : PartialSync Δ s₀ instrs) (hlead : Fair lead)
    {i j : Fin n} (hi : Correct s₀ instrs i) (hj : Correct s₀ instrs j)
    {t : Nat} {tr : Tx} (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S) :
    ∃ t' b, LNotarised f ((State.run s₀ instrs t').procs j).S b ∧ tr ∈ b.trStar := by
  classical
  have hΔ := hs.one_le
  -- max(GST, t) より後に始まる view v' で lead v' = i
  obtain ⟨v', hv'V, hlv'⟩ := hlead i
    ⟨(Finset.univ.sup fun r => (viewAt s₀ instrs r (max hs.GST.val t + 1)).val) + 1⟩
  have hbound : ∀ r, (viewAt s₀ instrs r (max hs.GST.val t + 1)).val < v'.val := fun r =>
    lt_of_lt_of_le (Nat.lt_succ_of_le
      (Finset.le_sup (f := fun r => (viewAt s₀ instrs r (max hs.GST.val t + 1)).val)
        (Finset.mem_univ r))) hv'V
  have hv'1 : 1 ≤ v'.val := le_trans (Nat.succ_le_succ (Nat.zero_le _)) hv'V
  have hreach : ∃ s, ∃ r, Correct s₀ instrs r ∧ v'.val ≤ (viewAt s₀ instrs r (s + 1)).val := by
    obtain ⟨s, hs'⟩ := progression hn hinit hh hb hs hi v'
    exact ⟨s, i, hi, hs'.trans (viewAt_le_succ i s)⟩
  have hfirst : FirstEntry s₀ instrs v' (Nat.find hreach) :=
    ⟨Nat.find_spec hreach, fun r t' hr h => Nat.find_min' hreach ⟨r, hr, h⟩⟩
  have hgst : max hs.GST.val t < Nat.find hreach := by
    obtain ⟨r, hr, h⟩ := Nat.find_spec hreach
    by_contra hle
    have h1 := viewAt_mono (s₀ := s₀) (instrs := instrs) r (Nat.add_le_add_right (not_lt.mp hle) 1)
    have h2 := hbound r
    omega
  have hlc : Correct s₀ instrs (lead v') := hlv' ▸ hi
  obtain ⟨e, R⟩ := leader_round hinit hh hs (le_refl Δ) hv'1 hlc hfirst (by omega)
  have hte := t_le_e hinit hh hb hs R
  -- 取引はブロックの Tr* に入る
  have htr' : tr ∈ (leaderBlockAt f lead s₀ instrs v' e).trStar := by
    apply mem_trStar_leaderBlock
    apply Algo.S_subset_st1 f (lead v') _
    rw [hlv']
    exact S_subset_run s₀ instrs i (by omega) htr
  -- 全正直者の票が j に届く
  have hvotes : ∀ r ∈ correctSet s₀ instrs, ∃ s, ∃ j',
      Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v' e)) j' ∈ (instrs s).actions r :=
    fun r hr => all_vote_leaderBlock hinit hh hb hs R hn (mem_correctSet.mp hr)
  obtain ⟨T, hT⟩ := exists_bound hvotes
  refine ⟨T + hs.GST.val + Δ + 1, leaderBlockAt f lead s₀ instrs v' e, ?_, htr'⟩
  right
  refine (card_correctSet hb).trans (Finset.card_le_card fun r hr => ?_)
  obtain ⟨s, hsT, j', hj'⟩ := hT r hr
  have hrc := mem_correctSet.mp hr
  have hj'' : Action.send (Msg.vote r (leaderBlockAt f lead s₀ instrs v' e)) j
      ∈ (instrs s).actions r := by
    rw [hh s r (hrc s)] at hj' ⊢
    exact Algo.send_all hj' j
  rw [mem_voters]
  exact delivered hinit hh hs hrc hj'' (by omega) (by omega)

end Minimmit
