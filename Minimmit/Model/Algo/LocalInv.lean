import Minimmit.Model.Algo.Stage

/-!
# 正直者の局所状態の不変量

Lemma 5.1・5.3 の核 `LocalInv`（S にある自分の票・nullify と view・notarised・nullified の関係）と、
提案についての `PropInv`。各段で保たれることを示す。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

/-! ### 正直者の局所状態の不変量
Lemma 5.1・5.3 の核。S にある自分の票・nullify と、view・notarised・nullified の関係。 -/

/-- 送信の途中（全員へ送る途中）でも保たれる部分。 -/
structure PreInv (f : Nat) (i : Fin n) (p : Processor n Tx) : Prop where
  /-- view は 1 以上。 -/
  view_pos : 1 ≤ p.view.val
  /-- 自分の票 (vote, c) が S にあれば、c は view 1 以上のブロックで、現在の view より前の
      ものか、現在の view のもので notarised に記録されている。 -/
  notar : ∀ c, Msg.vote i c ∈ p.S →
    1 ≤ c.view.val ∧ (c.view.val < p.view.val ∨ (c.view = p.view ∧ p.notarised = some c))
  /-- S にある自分の票で view が同じものは一致する。 -/
  unique : ∀ c c', Msg.vote i c ∈ p.S → Msg.vote i c' ∈ p.S → c.view = c'.view → c = c'
  /-- notarised のブロックは現在の view。 -/
  notar_view : ∀ c, p.notarised = some c → c.view = p.view
  /-- 自分の nullify(w) が S にあれば、1 ≤ w ≤ 現在の view。 -/
  null_view : ∀ w, Msg.nullify i w ∈ p.S → 1 ≤ w.val ∧ w.val ≤ p.view.val
  /-- 自分の現在の view の nullify が S にあれば nullified。 -/
  null_flag : Msg.nullify i p.view ∈ p.S → p.nullified = true
  /-- 自分の nullify(w) と、view w のブロック c への自分の票が両方 S にあるなら、
      S は view w で c 以外への進捗のなさの証拠を含む（24〜28 行で送った）。 -/
  null_vote : ∀ w c, Msg.nullify i w ∈ p.S → Msg.vote i c ∈ p.S → c.view = w →
    NoProgress f p.S w (some c)

/-- 正直者の局所状態の不変量。 -/
structure LocalInv (f : Nat) (i : Fin n) (p : Processor n Tx) : Prop extends PreInv f i p where
  /-- notarised のブロックへの自分の票は S にある。 -/
  notar_mem : ∀ c, p.notarised = some c → Msg.vote i c ∈ p.S
  /-- nullified なら、現在の view の自分の nullify は S にある。 -/
  null_mem : p.nullified = true → Msg.nullify i p.view ∈ p.S

namespace PreInv

variable {f : Nat} {i : Fin n} {p : Processor n Tx}

omit [DecidableEq Tx] in
/-- 関係する欄が等しければ移る。 -/
theorem congr (h : PreInv f i p) {q : Processor n Tx} (hv : q.view = p.view)
    (hn : q.notarised = p.notarised) (hnl : q.nullified = p.nullified) (hS : q.S = p.S) :
    PreInv f i q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]; exact h.view_pos
  · intro c hc; rw [hS] at hc; rw [hv, hn]; exact h.notar c hc
  · intro c c' hc hc'; rw [hS] at hc hc'; exact h.unique c c' hc hc'
  · intro c hc; rw [hn] at hc; rw [hv]; exact h.notar_view c hc
  · intro w hw; rw [hS] at hw; rw [hv]; exact h.null_view w hw
  · intro hw; rw [hv, hS] at hw; rw [hnl]; exact h.null_flag hw
  · intro w c hw hc hcw; rw [hS] at hw hc ⊢; exact h.null_vote w c hw hc hcw

omit [DecidableEq Tx] in
/-- view・notarised・nullified が変わらず S が増えても、増えた分に自分の票と nullify が
    無ければ保たれる。 -/
theorem of_grow (h : PreInv f i p) {q : Processor n Tx} (hv : q.view = p.view)
    (hn : q.notarised = p.notarised) (hnl : q.nullified = p.nullified) (hS : p.S ⊆ q.S)
    (hvote : ∀ c, Msg.vote i c ∈ q.S → Msg.vote i c ∈ p.S)
    (hnull : ∀ w, Msg.nullify i w ∈ q.S → Msg.nullify i w ∈ p.S) : PreInv f i q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]; exact h.view_pos
  · intro c hc; rw [hv, hn]; exact h.notar c (hvote c hc)
  · intro c c' hc hc'; exact h.unique c c' (hvote c hc) (hvote c' hc')
  · intro c hc; rw [hn] at hc; rw [hv]; exact h.notar_view c hc
  · intro w hw; rw [hv]; exact h.null_view w (hnull w hw)
  · intro hw; rw [hv] at hw; rw [hnl]; exact h.null_flag (hnull _ hw)
  · intro w c hw hc hcw; exact (h.null_vote w c (hnull w hw) (hvote c hc) hcw).mono hS

omit [DecidableEq Tx] in
theorem of_sgrows (h : PreInv f i p) {q : Processor n Tx} (hg : p.SGrows q)
    (hvote : ∀ c, Msg.vote i c ∈ q.S → Msg.vote i c ∈ p.S)
    (hnull : ∀ w, Msg.nullify i w ∈ q.S → Msg.nullify i w ∈ p.S) : PreInv f i q :=
  h.of_grow hg.view hg.notarised hg.nullified hg.S hvote hnull

theorem mem_S_send_iff_of_ne (i : Fin n) (p : Processor n Tx) {m m' : Msg n Tx} (j : Fin n)
    (hne : m' ≠ m) : m' ∈ (p.send i m j).S ↔ m' ∈ p.S := by
  rw [Processor.send_S]
  split_ifs
  · simp [Finset.mem_insert, hne]
  · exact Iff.rfl

/-- 自分の票でも自分の nullify でもない message の送信は不変量を保つ。 -/
theorem send_of_not_own (h : PreInv f i p) {m : Msg n Tx} (hv : ∀ b, m ≠ Msg.vote i b)
    (hn : ∀ v, m ≠ Msg.nullify i v) (j : Fin n) : PreInv f i (p.send i m j) := by
  refine h.of_grow (Processor.send_view i p m j)
    (Processor.send_notarised_of_not_vote i p m j fun b hb => absurd hb (hv b))
    (Processor.send_nullified_of_not_nullify i p m j fun v hv' => absurd hv' (hn v))
    (Processor.S_subset_send i p m j) (fun c hc => ?_) (fun w hw => ?_)
  · exact (mem_S_send_iff_of_ne i p j fun h' => hv c h'.symm).mp hc
  · exact (mem_S_send_iff_of_ne i p j fun h' => hn w h'.symm).mp hw

/-- S にある message の再送は、view・notarised・nullified・S を変えない。 -/
theorem send_of_mem_eq (h : PreInv f i p) {m : Msg n Tx} (hm : m ∈ p.S) (j : Fin n) :
    (p.send i m j).notarised = p.notarised ∧ (p.send i m j).nullified = p.nullified
      ∧ (p.send i m j).S = p.S := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases hv : ∃ b, m = Msg.vote i b
    · obtain ⟨b, rfl⟩ := hv
      rw [Processor.send_vote_notarised]
      split_ifs with hb
      · exact ((h.notar b hm).2.resolve_left (by rw [hb]; exact lt_irrefl _)).2.symm
      · rfl
    · exact Processor.send_notarised_of_not_vote i p m j fun b hb => absurd ⟨b, hb⟩ hv
  · by_cases hn : ∃ v, m = Msg.nullify i v
    · obtain ⟨v, rfl⟩ := hn
      rw [Processor.send_nullify_nullified]
      split_ifs with hv
      · subst hv; exact (h.null_flag hm).symm
      · rfl
    · exact Processor.send_nullified_of_not_nullify i p m j fun v hv => absurd ⟨v, hv⟩ hn
  · rw [Processor.send_S]; split_ifs <;> simp [Finset.insert_eq_of_mem hm]

theorem send_of_mem (h : PreInv f i p) {m : Msg n Tx} (hm : m ∈ p.S) (j : Fin n) :
    PreInv f i (p.send i m j) :=
  let ⟨hn, hnl, hS⟩ := h.send_of_mem_eq hm j
  h.congr (Processor.send_view i p m j) hn hnl hS

/-- 現在の view のブロック b への自分の票。notarised が ⊥ か既に b で、現在の view の
    nullify を送っていないとき。 -/
theorem send_vote (h : PreInv f i p) {b : Block Tx} (hb : b.view = p.view)
    (hn : p.notarised = none ∨ p.notarised = some b) (hnn : Msg.nullify i p.view ∉ p.S)
    (j : Fin n) : PreInv f i (p.send i (Msg.vote i b) j) := by
  have hS : ∀ c, Msg.vote i c ∈ (p.send i (Msg.vote i b) j).S → c = b ∨ Msg.vote i c ∈ p.S := by
    intro c hc
    rw [Processor.send_S] at hc
    split_ifs at hc
    · rcases Finset.mem_insert.mp hc with hc | hc
      · exact Or.inl (by cases hc; rfl)
      · exact Or.inr hc
    · exact Or.inr hc
  have hN : ∀ w, Msg.nullify i w ∈ (p.send i (Msg.vote i b) j).S → Msg.nullify i w ∈ p.S :=
    fun w hw => (mem_S_send_iff_of_ne i p j (by simp)).mp hw
  have hcur : ∀ c, Msg.vote i c ∈ p.S → c.view = p.view → c = b := by
    intro c hc hcv
    rcases (h.notar c hc).2 with hlt | ⟨_, hcn⟩
    · rw [hcv] at hlt; exact absurd hlt (lt_irrefl _)
    · rcases hn with hn | hn
      · rw [hn] at hcn; cases hcn
      · rw [hn] at hcn; exact (Option.some.inj hcn).symm
  have hview := Processor.send_view i p (Msg.vote i b) j
  have hnot := Processor.send_vote_notarised i p b j
  rw [if_pos hb] at hnot
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hview]; exact h.view_pos
  · intro c hc
    rw [hview, hnot]
    rcases hS c hc with rfl | hc
    · exact ⟨by rw [hb]; exact h.view_pos, Or.inr ⟨hb, rfl⟩⟩
    · obtain ⟨hpos, hlt | ⟨hce, _⟩⟩ := h.notar c hc
      · exact ⟨hpos, Or.inl hlt⟩
      · exact ⟨hpos, Or.inr ⟨hce, congrArg some (hcur c hc hce).symm⟩⟩
  · intro c c' hc hc' hv
    rcases hS c hc with hcb | hc
    · rcases hS c' hc' with hcb' | hc'
      · exact hcb.trans hcb'.symm
      · rw [hcb]; exact (hcur c' hc' (hv.symm.trans (hcb ▸ hb))).symm
    · rcases hS c' hc' with hcb' | hc'
      · rw [hcb']; exact hcur c hc (hv.trans (hcb' ▸ hb))
      · exact h.unique c c' hc hc' hv
  · intro c hc; rw [hnot] at hc; rw [hview, ← Option.some.inj hc]; exact hb
  · intro w hw; rw [hview]; exact h.null_view w (hN w hw)
  · intro hw; rw [hview] at hw; exact absurd (hN _ hw) hnn
  · intro w c hw hc hcw
    have hw' := hN w hw
    rcases hS c hc with rfl | hc
    · have hwv : w = p.view := hcw.symm.trans hb
      rw [hwv] at hw'
      exact absurd hw' hnn
    · exact (h.null_vote w c hw' hc hcw).mono (Processor.S_subset_send i p _ j)

/-- 現在の view の nullify。notarised が ⊥ か、notarised のブロック以外への進捗のなさの
    証拠があるとき。 -/
theorem send_nullify (h : PreInv f i p)
    (hH : p.notarised = none ∨ ∃ c₀, p.notarised = some c₀ ∧ NoProgress f p.S p.view (some c₀))
    (j : Fin n) : PreInv f i (p.send i (Msg.nullify i p.view) j) := by
  have hV : ∀ c, Msg.vote i c ∈ (p.send i (Msg.nullify i p.view) j).S → Msg.vote i c ∈ p.S :=
    fun c hc => (mem_S_send_iff_of_ne i p j (by simp)).mp hc
  have hN : ∀ w, Msg.nullify i w ∈ (p.send i (Msg.nullify i p.view) j).S →
      w = p.view ∨ Msg.nullify i w ∈ p.S := by
    intro w hw
    rw [Processor.send_S] at hw
    split_ifs at hw
    · rcases Finset.mem_insert.mp hw with hw | hw
      · exact Or.inl (by cases hw; rfl)
      · exact Or.inr hw
    · exact Or.inr hw
  have hview := Processor.send_view i p (Msg.nullify i p.view) j
  have hnot := Processor.send_notarised_of_not_vote i p (Msg.nullify i p.view) j
    fun b hb => by cases hb
  have hnl := Processor.send_nullify_nullified i p p.view j
  rw [if_pos rfl] at hnl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hview]; exact h.view_pos
  · intro c hc; rw [hview, hnot]; exact h.notar c (hV c hc)
  · intro c c' hc hc'; exact h.unique c c' (hV c hc) (hV c' hc')
  · intro c hc; rw [hnot] at hc; rw [hview]; exact h.notar_view c hc
  · intro w hw
    rw [hview]
    rcases hN w hw with rfl | hw
    · exact ⟨h.view_pos, le_refl _⟩
    · exact h.null_view w hw
  · intro _; exact hnl
  · intro w c hw hc hcw
    have hc' := hV c hc
    rcases hN w hw with rfl | hw
    · obtain ⟨_, hlt | ⟨_, hcn⟩⟩ := h.notar c hc'
      · rw [hcw] at hlt; exact absurd hlt (lt_irrefl _)
      · rcases hH with hH | ⟨c₀, hc₀, hnp⟩
        · rw [hH] at hcn; cases hcn
        · rw [hc₀] at hcn
          rw [← Option.some.inj hcn]
          exact hnp.mono (Processor.S_subset_send i p _ j)
    · exact (h.null_vote w c hw hc' hcw).mono (Processor.S_subset_send i p _ j)

omit [DecidableEq Tx] in
/-- 次の view へ進んでも保たれる。 -/
theorem progress (h : PreInv f i p) : PreInv f i p.progress := by
  refine ⟨Nat.le_succ_of_le h.view_pos, ?_, fun c c' hc hc' hv => h.unique c c' hc hc' hv,
    ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨hpos, hlt | ⟨hce, _⟩⟩ := h.notar c hc
    · exact ⟨hpos, Or.inl (Nat.lt_succ_of_lt hlt)⟩
    · exact ⟨hpos, Or.inl (by simp only [Processor.progress]; rw [hce]; exact Nat.lt_succ_self _)⟩
  · intro c hc; simp [Processor.progress] at hc
  · intro w hw
    obtain ⟨h1, h2⟩ := h.null_view w hw
    exact ⟨h1, Nat.le_succ_of_le h2⟩
  · intro hw
    have := (h.null_view _ hw).2
    simp only [Processor.progress] at this
    omega
  · intro w c hw hc hcw; exact h.null_vote w c hw hc hcw

/-! #### 全員への送信 -/

theorem foldl_send_of_not_own (h : PreInv f i p) {m : Msg n Tx} (hv : ∀ b, m ≠ Msg.vote i b)
    (hn : ∀ v, m ≠ Msg.nullify i v) (l : List (Fin n)) :
    PreInv f i (l.foldl (fun p j => p.send i m j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih => exact ih (h.send_of_not_own hv hn j)

theorem foldl_send_of_mem_eq (h : PreInv f i p) {m : Msg n Tx} (hm : m ∈ p.S) (l : List (Fin n)) :
    PreInv f i (l.foldl (fun p j => p.send i m j) p)
      ∧ (l.foldl (fun p j => p.send i m j) p).notarised = p.notarised
      ∧ (l.foldl (fun p j => p.send i m j) p).nullified = p.nullified
      ∧ (l.foldl (fun p j => p.send i m j) p).S = p.S := by
  induction l generalizing p with
  | nil => exact ⟨h, rfl, rfl, rfl⟩
  | cons j l ih =>
    obtain ⟨hn, hnl, hS⟩ := h.send_of_mem_eq hm j
    obtain ⟨h', hn', hnl', hS'⟩ := ih (h.send_of_mem hm j) (hS ▸ hm)
    exact ⟨h', hn'.trans hn, hnl'.trans hnl, hS'.trans hS⟩

theorem foldl_send_nullified_of_not_nullify {m : Msg n Tx} (hn : ∀ v, m ≠ Msg.nullify i v)
    (l : List (Fin n)) (p : Processor n Tx) :
    (l.foldl (fun p j => p.send i m j) p).nullified = p.nullified := by
  induction l generalizing p with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons, ih,
      Processor.send_nullified_of_not_nullify i p m j fun v hv => absurd hv (hn v)]

theorem foldl_send_view (m : Msg n Tx) (l : List (Fin n)) (p : Processor n Tx) :
    (l.foldl (fun p j => p.send i m j) p).view = p.view := by
  induction l generalizing p with
  | nil => rfl
  | cons j l ih => rw [List.foldl_cons, ih, Processor.send_view]

theorem foldl_send_vote (h : PreInv f i p) {b : Block Tx} (hb : b.view = p.view)
    (hn : p.notarised = none ∨ p.notarised = some b) (hnn : Msg.nullify i p.view ∉ p.S)
    (l : List (Fin n)) : PreInv f i (l.foldl (fun p j => p.send i (Msg.vote i b) j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih =>
    refine ih (h.send_vote hb hn hnn j) (by rw [Processor.send_view]; exact hb) ?_ ?_
    · right; rw [Processor.send_vote_notarised, if_pos hb]
    · rw [Processor.send_view]
      exact fun hw => hnn ((mem_S_send_iff_of_ne i p j (by simp)).mp hw)

theorem foldl_send_vote_notarised {b : Block Tx} (hb : b.view = p.view) {l : List (Fin n)}
    (hl : l ≠ []) : (l.foldl (fun p j => p.send i (Msg.vote i b) j) p).notarised = some b := by
  induction l generalizing p with
  | nil => exact absurd rfl hl
  | cons j l ih =>
    rw [List.foldl_cons]
    rcases l with _ | ⟨j', l⟩
    · simp only [List.foldl_nil]; rw [Processor.send_vote_notarised, if_pos hb]
    · exact ih (by rw [Processor.send_view]; exact hb) (List.cons_ne_nil _ _)

theorem foldl_send_nullify (h : PreInv f i p) {v : View} (hv : v = p.view)
    (hH : p.notarised = none ∨ ∃ c₀, p.notarised = some c₀ ∧ NoProgress f p.S v (some c₀))
    (l : List (Fin n)) :
    PreInv f i (l.foldl (fun p j => p.send i (Msg.nullify i v) j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih =>
    subst hv
    rw [List.foldl_cons]
    refine ih (h.send_nullify hH j) (Processor.send_view i p _ j).symm ?_
    rw [Processor.send_notarised_of_not_vote i p _ j fun b hb => by cases hb]
    exact hH.imp_right fun ⟨c₀, hc₀, hnp⟩ =>
      ⟨c₀, hc₀, hnp.mono (Processor.S_subset_send i p _ j)⟩

theorem foldl_send_notarised_of_not_vote {m : Msg n Tx} (hv : ∀ b, m ≠ Msg.vote i b)
    (l : List (Fin n)) (p : Processor n Tx) :
    (l.foldl (fun p j => p.send i m j) p).notarised = p.notarised := by
  induction l generalizing p with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons, ih, Processor.send_notarised_of_not_vote i p m j fun b hb => absurd hb (hv b)]

end PreInv

namespace LocalInv

variable {f : Nat} {i : Fin n} {p : Processor n Tx}

omit [DecidableEq Tx] in
theorem of_grow (h : LocalInv f i p) {q : Processor n Tx} (hv : q.view = p.view)
    (hn : q.notarised = p.notarised) (hnl : q.nullified = p.nullified) (hS : p.S ⊆ q.S)
    (hvote : ∀ c, Msg.vote i c ∈ q.S → Msg.vote i c ∈ p.S)
    (hnull : ∀ w, Msg.nullify i w ∈ q.S → Msg.nullify i w ∈ p.S) : LocalInv f i q :=
  ⟨h.toPreInv.of_grow hv hn hnl hS hvote hnull, fun c hc => hS (h.notar_mem c (hn ▸ hc)),
   fun hq => by rw [hv]; exact hS (h.null_mem (hnl ▸ hq))⟩

omit [DecidableEq Tx] in
theorem of_sgrows (h : LocalInv f i p) {q : Processor n Tx} (hg : p.SGrows q)
    (hvote : ∀ c, Msg.vote i c ∈ q.S → Msg.vote i c ∈ p.S)
    (hnull : ∀ w, Msg.nullify i w ∈ q.S → Msg.nullify i w ∈ p.S) : LocalInv f i q :=
  h.of_grow hg.view hg.notarised hg.nullified hg.S hvote hnull

omit [DecidableEq Tx] in
theorem tick (h : LocalInv f i p) : LocalInv f i p.tick :=
  h.of_grow rfl rfl rfl (Finset.Subset.refl _) (fun _ hc => hc) (fun _ hw => hw)

omit [DecidableEq Tx] in
theorem progress (h : LocalInv f i p) : LocalInv f i p.progress :=
  ⟨h.toPreInv.progress, fun c hc => by simp [Processor.progress] at hc,
   fun hq => by simp [Processor.progress] at hq⟩

theorem disseminate_of_not_own (h : LocalInv f i p) {m : Msg n Tx} (hv : ∀ b, m ≠ Msg.vote i b)
    (hn : ∀ v, m ≠ Msg.nullify i v) : LocalInv f i (disseminate i p m).1 := by
  rw [disseminate_fst]
  refine ⟨h.toPreInv.foldl_send_of_not_own hv hn _, fun c hc => ?_, fun hq => ?_⟩
  · rw [PreInv.foldl_send_notarised_of_not_vote hv] at hc
    exact S_subset_foldl_send i m _ p (h.notar_mem c hc)
  · rw [PreInv.foldl_send_nullified_of_not_nullify hn] at hq
    rw [PreInv.foldl_send_view]
    exact S_subset_foldl_send i m _ p (h.null_mem hq)

theorem disseminate_of_mem (h : LocalInv f i p) {m : Msg n Tx} (hm : m ∈ p.S) :
    LocalInv f i (disseminate i p m).1 := by
  rw [disseminate_fst]
  obtain ⟨h', hn, hnl, hS⟩ := h.toPreInv.foldl_send_of_mem_eq hm (List.finRange n)
  exact ⟨h', fun c hc => by rw [hS]; exact h.notar_mem c (hn ▸ hc),
    fun hq => by rw [hS, PreInv.foldl_send_view]; exact h.null_mem (hnl ▸ hq)⟩

theorem disseminate_vote (h : LocalInv f i p) {b : Block Tx} (hb : b.view = p.view)
    (hn : p.notarised = none ∨ p.notarised = some b) (hnn : Msg.nullify i p.view ∉ p.S) :
    LocalInv f i (disseminate i p (Msg.vote i b)).1 := by
  have hmem := mem_S_disseminate_fst i p (Msg.vote i b)
  rw [disseminate_fst] at hmem ⊢
  refine ⟨h.toPreInv.foldl_send_vote hb hn hnn _, fun c hc => ?_, fun hq => ?_⟩
  · rw [PreInv.foldl_send_vote_notarised hb (List.ne_nil_of_mem (List.mem_finRange i))] at hc
    rw [← Option.some.inj hc]
    exact hmem
  · rw [PreInv.foldl_send_nullified_of_not_nullify (fun v hv => by cases hv)] at hq
    rw [PreInv.foldl_send_view]
    exact S_subset_foldl_send i _ _ p (h.null_mem hq)

theorem disseminate_nullify (h : LocalInv f i p)
    (hH : p.notarised = none ∨ ∃ c₀, p.notarised = some c₀ ∧ NoProgress f p.S p.view (some c₀)) :
    LocalInv f i (disseminate i p (Msg.nullify i p.view)).1 := by
  have hmem := mem_S_disseminate_fst i p (Msg.nullify i p.view)
  rw [disseminate_fst] at hmem ⊢
  refine ⟨h.toPreInv.foldl_send_nullify rfl hH _, fun c hc => ?_, fun _ => ?_⟩
  · rw [PreInv.foldl_send_notarised_of_not_vote (fun b hb => by cases hb)] at hc
    exact S_subset_foldl_send i _ _ p (h.notar_mem c hc)
  · rw [PreInv.foldl_send_view]; exact hmem

theorem disseminateAll_of_mem (h : LocalInv f i p) {ms : List (Msg n Tx)} (hm : ∀ m ∈ ms, m ∈ p.S) :
    LocalInv f i (disseminateAll i p ms).1 := by
  rw [disseminateAll_fst]
  induction ms generalizing p with
  | nil => exact h
  | cons m ms ih =>
    exact ih (h.disseminate_of_mem (hm m (List.mem_cons_self ..))) fun m' hm' =>
      S_subset_disseminate_fst i p m (hm m' (List.mem_cons_of_mem _ hm'))

/-! #### 各段 -/

theorem forwardNew (h : LocalInv f i p) : LocalInv f i (forwardNew f i p).1 := by
  rw [forwardNew_eq]
  exact h.disseminateAll_of_mem fun m hm => mem_S_of_mem_forwardMsgs hm

theorem propose (h : LocalInv f i p) (lead : View → Fin n) :
    LocalInv f i (propose f lead i p).1 := by
  unfold Algo.propose
  split_ifs
  · exact h.disseminate_of_not_own (fun _ h => by cases h) (fun _ h => by cases h)
  · exact h

theorem voteProposal (h : LocalInv f i p) (lead : View → Fin n) :
    LocalInv f i (voteProposal f lead i p).1 := by
  unfold Algo.voteProposal
  rcases proposals lead p.S p.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · exact h
  · simp only
    split_ifs with hg
    · refine h.disseminate_vote hg.1.view (Or.inl hg.2.1) fun hw => ?_
      have := h.null_flag hw
      rw [hg.2.2] at this
      cases this
    · exact h
  · exact h

theorem nullifyTimeout (h : LocalInv f i p) (Δ : Nat) : LocalInv f i (nullifyTimeout Δ i p).1 := by
  unfold Algo.nullifyTimeout
  split_ifs with hg
  · exact h.disseminate_nullify (Or.inl hg.2.2)
  · exact h

theorem advanceM (h : LocalInv f i p) : LocalInv f i (advanceM f i p).1 := by
  unfold Algo.advanceM
  rcases hm : mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · exact h
  · simp only
    split_ifs with hg
    · refine (h.disseminate_vote (mem_mNotarisedAt (hm ▸ List.mem_cons_self ..)).1
        (Or.inl hg.1) fun hw => ?_).progress
      have := h.null_flag hw
      rw [hg.2] at this
      cases this
    · exact h.progress

theorem advanceOnce (h : LocalInv f i p) : LocalInv f i (advanceOnce f i p).1 := by
  rw [advanceOnce_eq]; split_ifs
  · exact h.progress
  · exact h.advanceM

theorem climb (h : LocalInv f i p) (fuel : Nat) : LocalInv f i (climb f i fuel p).1 := by
  induction fuel generalizing p with
  | zero => exact h
  | succ fuel ih =>
    simp only [Algo.climb]; split_ifs
    · exact ih h.advanceOnce
    · exact h

theorem nullifyNoProgress (h : LocalInv f i p) : LocalInv f i (nullifyNoProgress f i p).1 := by
  unfold Algo.nullifyNoProgress
  split_ifs with hg
  · obtain ⟨c₀, hc₀⟩ := Option.ne_none_iff_exists'.mp hg.2.1
    refine h.disseminate_nullify (Or.inr ⟨c₀, hc₀, ?_⟩)
    rw [← hc₀]; exact hg.2.2
  · exact h

/-- Algorithm 1 の 1 スロット分の動作は不変量を保つ。 -/
theorem stepPair (h : LocalInv f i p) (Δ : Nat) (lead : View → Fin n) :
    LocalInv f i (stepPair f Δ lead i p).1 :=
  (((((h.climb _).propose lead).voteProposal lead).nullifyTimeout Δ).nullifyNoProgress).forwardNew

end LocalInv


/-! ### 自分の提案についての不変量 -/

/-- S にある自分の署名付きブロックと、view・proposed の関係。 -/
structure PropInv (i : Fin n) (p : Processor n Tx) : Prop where
  /-- 自分のブロックの view は現在の view 以下。 -/
  prop_view : ∀ b, Msg.block i b ∈ p.S → b.view.val ≤ p.view.val
  /-- 現在の view の自分のブロックが S にあれば proposed。 -/
  prop_flag : ∀ b, Msg.block i b ∈ p.S → b.view = p.view → p.proposed = true
  /-- S にある自分のブロックで view が同じものは一致する。 -/
  prop_unique : ∀ b b', Msg.block i b ∈ p.S → Msg.block i b' ∈ p.S → b.view = b'.view → b = b'

namespace PropInv

variable {f : Nat} {i : Fin n} {p : Processor n Tx}

omit [DecidableEq Tx] in
theorem of_grow (h : PropInv i p) {q : Processor n Tx} (hv : q.view = p.view)
    (hp : q.proposed = p.proposed) (hblock : ∀ b, Msg.block i b ∈ q.S → Msg.block i b ∈ p.S) :
    PropInv i q := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb; rw [hv]; exact h.prop_view b (hblock b hb)
  · intro b hb hbv; rw [hp]; rw [hv] at hbv; exact h.prop_flag b (hblock b hb) hbv
  · intro b b' hb hb'; exact h.prop_unique b b' (hblock b hb) (hblock b' hb')

omit [DecidableEq Tx] in
theorem of_sgrows (h : PropInv i p) {q : Processor n Tx} (hg : p.SGrows q)
    (hblock : ∀ b, Msg.block i b ∈ q.S → Msg.block i b ∈ p.S) : PropInv i q :=
  h.of_grow hg.view hg.proposed hblock

omit [DecidableEq Tx] in
theorem tick (h : PropInv i p) : PropInv i p.tick := h.of_grow rfl rfl fun _ hb => hb

omit [DecidableEq Tx] in
theorem progress (h : PropInv i p) : PropInv i p.progress := by
  refine ⟨?_, ?_, fun b b' hb hb' => h.prop_unique b b' hb hb'⟩
  · intro b hb
    have := h.prop_view b hb
    simp only [Processor.progress]; omega
  · intro b hb hbv
    have := h.prop_view b hb
    rw [hbv] at this
    simp only [Processor.progress] at this
    omega

theorem send_of_not_block (h : PropInv i p) {m : Msg n Tx} (hm : ∀ b, m ≠ Msg.block i b)
    (j : Fin n) : PropInv i (p.send i m j) := by
  refine h.of_grow (Processor.send_view i p m j)
    (Processor.send_proposed_of_not_block i p m j fun b hb => absurd hb (hm b)) fun b hb => ?_
  exact (PreInv.mem_S_send_iff_of_ne i p j fun h' => hm b h'.symm).mp hb

theorem send_of_mem (h : PropInv i p) {m : Msg n Tx} (hm : m ∈ p.S) (j : Fin n) :
    PropInv i (p.send i m j) := by
  have hS : (p.send i m j).S = p.S := by
    rw [Processor.send_S]; split_ifs <;> simp [Finset.insert_eq_of_mem hm]
  refine ⟨?_, ?_, ?_⟩
  · intro b hb; rw [hS] at hb; rw [Processor.send_view]; exact h.prop_view b hb
  · intro b hb hbv
    rw [hS] at hb; rw [Processor.send_view] at hbv
    have := h.prop_flag b hb hbv
    by_cases hmb : ∃ b', m = Msg.block i b'
    · obtain ⟨b', rfl⟩ := hmb
      rw [Processor.send_block_proposed]
      split_ifs
      · rfl
      · exact this
    · rw [Processor.send_proposed_of_not_block i p m j fun b' hb' => absurd ⟨b', hb'⟩ hmb]
      exact this
  · intro b b' hb hb'; rw [hS] at hb hb'; exact h.prop_unique b b' hb hb'

/-- 現在の view のブロックの送信。同じ view の自分のブロックは S にそれしかない。 -/
theorem send_block (h : PropInv i p) {b : Block Tx} (hb : b.view = p.view)
    (huniq : ∀ b', Msg.block i b' ∈ p.S → b'.view = p.view → b' = b) (j : Fin n) :
    PropInv i (p.send i (Msg.block i b) j) := by
  have hS : ∀ b', Msg.block i b' ∈ (p.send i (Msg.block i b) j).S →
      b' = b ∨ Msg.block i b' ∈ p.S := by
    intro b' hb'
    rw [Processor.send_S] at hb'
    split_ifs at hb'
    · rcases Finset.mem_insert.mp hb' with hb' | hb'
      · exact Or.inl (by cases hb'; rfl)
      · exact Or.inr hb'
    · exact Or.inr hb'
  have hview := Processor.send_view i p (Msg.block i b) j
  refine ⟨?_, ?_, ?_⟩
  · intro b' hb'
    rw [hview]
    rcases hS b' hb' with rfl | hb'
    · rw [hb]
    · exact h.prop_view b' hb'
  · intro b' _ _
    rw [Processor.send_block_proposed, if_pos hb]
  · intro b' b'' hb' hb'' hvv
    rcases hS b' hb' with rfl | hb₁ <;> rcases hS b'' hb'' with rfl | hb₂
    · rfl
    · exact (huniq b'' hb₂ (hvv.symm.trans hb)).symm
    · exact huniq b' hb₁ (hvv.trans hb)
    · exact h.prop_unique b' b'' hb₁ hb₂ hvv

theorem foldl_send_of_not_block (h : PropInv i p) {m : Msg n Tx} (hm : ∀ b, m ≠ Msg.block i b)
    (l : List (Fin n)) : PropInv i (l.foldl (fun p j => p.send i m j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih => exact ih (h.send_of_not_block hm j)

theorem foldl_send_of_mem (h : PropInv i p) {m : Msg n Tx} (hm : m ∈ p.S) (l : List (Fin n)) :
    PropInv i (l.foldl (fun p j => p.send i m j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih => exact ih (h.send_of_mem hm j) (Processor.S_subset_send i p m j hm)

theorem foldl_send_block (h : PropInv i p) {b : Block Tx} (hb : b.view = p.view)
    (huniq : ∀ b', Msg.block i b' ∈ p.S → b'.view = p.view → b' = b) (l : List (Fin n)) :
    PropInv i (l.foldl (fun p j => p.send i (Msg.block i b) j) p) := by
  induction l generalizing p with
  | nil => exact h
  | cons j l ih =>
    refine ih (h.send_block hb huniq j) (by rw [Processor.send_view]; exact hb) ?_
    intro b' hb' hbv
    rw [Processor.send_view] at hbv
    rw [Processor.send_S] at hb'
    split_ifs at hb'
    · rcases Finset.mem_insert.mp hb' with hb' | hb'
      · cases hb'; rfl
      · exact huniq b' hb' hbv
    · exact huniq b' hb' hbv

theorem disseminate_of_not_block (h : PropInv i p) {m : Msg n Tx} (hm : ∀ b, m ≠ Msg.block i b) :
    PropInv i (disseminate i p m).1 := by
  rw [disseminate_fst]; exact h.foldl_send_of_not_block hm _

theorem disseminate_of_mem (h : PropInv i p) {m : Msg n Tx} (hm : m ∈ p.S) :
    PropInv i (disseminate i p m).1 := by
  rw [disseminate_fst]; exact h.foldl_send_of_mem hm _

/-- まだ提案していないときの、現在の view のブロックの提案。 -/
theorem disseminate_block (h : PropInv i p) {b : Block Tx} (hb : b.view = p.view)
    (hp : p.proposed = false) : PropInv i (disseminate i p (Msg.block i b)).1 := by
  rw [disseminate_fst]
  refine h.foldl_send_block hb (fun b' hb' hbv => ?_) _
  have := h.prop_flag b' hb' hbv
  rw [hp] at this; cases this

theorem disseminateAll_of_mem (h : PropInv i p) {ms : List (Msg n Tx)} (hm : ∀ m ∈ ms, m ∈ p.S) :
    PropInv i (disseminateAll i p ms).1 := by
  rw [disseminateAll_fst]
  induction ms generalizing p with
  | nil => exact h
  | cons m ms ih =>
    exact ih (h.disseminate_of_mem (hm m (List.mem_cons_self ..))) fun m' hm' =>
      S_subset_disseminate_fst i p m (hm m' (List.mem_cons_of_mem _ hm'))

theorem forwardNew (h : PropInv i p) : PropInv i (forwardNew f i p).1 := by
  rw [forwardNew_eq]
  exact h.disseminateAll_of_mem fun m hm => mem_S_of_mem_forwardMsgs hm

theorem propose (h : PropInv i p) (lead : View → Fin n) : PropInv i (propose f lead i p).1 := by
  unfold Algo.propose
  split_ifs with hg
  · exact h.disseminate_block rfl hg.2
  · exact h

theorem voteProposal (h : PropInv i p) (lead : View → Fin n) :
    PropInv i (voteProposal f lead i p).1 := by
  unfold Algo.voteProposal
  rcases proposals lead p.S p.view with _ | ⟨b, _ | ⟨b', l⟩⟩
  · exact h
  · simp only
    split_ifs
    · exact h.disseminate_of_not_block fun _ h => by cases h
    · exact h
  · exact h

theorem nullifyTimeout (h : PropInv i p) (Δ : Nat) : PropInv i (nullifyTimeout Δ i p).1 := by
  unfold Algo.nullifyTimeout
  split_ifs
  · exact h.disseminate_of_not_block fun _ h => by cases h
  · exact h

theorem advanceM (h : PropInv i p) : PropInv i (advanceM f i p).1 := by
  unfold Algo.advanceM
  rcases mNotarisedAt f p.S p.view with _ | ⟨b, l⟩
  · exact h
  · simp only
    split_ifs
    · exact (h.disseminate_of_not_block fun _ h => by cases h).progress
    · exact h.progress

theorem advanceOnce (h : PropInv i p) : PropInv i (advanceOnce f i p).1 := by
  rw [advanceOnce_eq]; split_ifs
  · exact h.progress
  · exact h.advanceM

theorem climb (h : PropInv i p) (fuel : Nat) : PropInv i (climb f i fuel p).1 := by
  induction fuel generalizing p with
  | zero => exact h
  | succ fuel ih =>
    simp only [Algo.climb]; split_ifs
    · exact ih h.advanceOnce
    · exact h

theorem nullifyNoProgress (h : PropInv i p) : PropInv i (nullifyNoProgress f i p).1 := by
  unfold Algo.nullifyNoProgress
  split_ifs
  · exact h.disseminate_of_not_block fun _ h => by cases h
  · exact h

/-- Algorithm 1 の 1 スロット分の動作は不変量を保つ。 -/
theorem stepPair (h : PropInv i p) (Δ : Nat) (lead : View → Fin n) :
    PropInv i (stepPair f Δ lead i p).1 :=
  (((((h.climb _).propose lead).voteProposal lead).nullifyTimeout Δ).nullifyNoProgress).forwardNew

end PropInv

end Algo

end Minimmit
