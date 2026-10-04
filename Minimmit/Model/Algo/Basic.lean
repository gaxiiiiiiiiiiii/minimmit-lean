import Minimmit.Model.Certificate.Basic
import Minimmit.Model.Transition.Execute
import Minimmit.Model.Certificate.Mono
import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort

/-!
# Algorithm 1

局所状態から 1 スロット分の動作の列を返す関数 `Algo.step` と、その各部分の関数（16〜21 行の
`climb`、5〜7 行の `propose`、9〜11 行の `voteProposal`、13〜14 行の `nullifyTimeout`、
24〜28 行の `nullifyNoProgress`、2〜3 行の `forwardNew`）、各部分が共通して使う補助関数。
`climb` の停止性の証明に使う補題もここに置く。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

/-! ## 補助関数 -/

/-! ### 送信
動作の列を組み立てながら、`Processor.send` で局所状態にも同じ効果を与える。 -/

/-- m を全員へ送る。自分宛も含み、`Processor.send` が即時受信にする。 -/
def disseminate (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    Processor n Tx × List (Action n Tx) :=
  (List.finRange n).foldl
    (fun (pa : Processor n Tx × List (Action n Tx)) j =>
      (pa.1.send i m j, pa.2 ++ [Action.send m j]))
    (p, [])

/-- ms の各メッセージを順に全員へ送る。 -/
def disseminateAll (i : Fin n) (p : Processor n Tx) (ms : List (Msg n Tx)) :
    Processor n Tx × List (Action n Tx) :=
  ms.foldl
    (fun (pa : Processor n Tx × List (Action n Tx)) m =>
      let r := disseminate i pa.1 m
      (r.1, pa.2 ++ r.2))
    (p, [])

theorem disseminate_snd (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    (disseminate i p m).2 = (List.finRange n).map (Action.send m) := by
  simp only [disseminate]
  suffices h : ∀ (l : List (Fin n)) (p : Processor n Tx) (acc : List (Action n Tx)),
      (l.foldl (fun (pa : Processor n Tx × List (Action n Tx)) j =>
        (pa.1.send i m j, pa.2 ++ [Action.send m j])) (p, acc)).2 = acc ++ l.map (Action.send m) by
    simpa using h (List.finRange n) p []
  intro l
  induction l with
  | nil => simp
  | cons j l ih => intro p acc; simp [ih]

theorem disseminate_fst (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    (disseminate i p m).1 = (List.finRange n).foldl (fun p j => p.send i m j) p := by
  simp only [disseminate]
  suffices h : ∀ (l : List (Fin n)) (p : Processor n Tx) (acc : List (Action n Tx)),
      (l.foldl (fun (pa : Processor n Tx × List (Action n Tx)) j =>
        (pa.1.send i m j, pa.2 ++ [Action.send m j])) (p, acc)).1
        = l.foldl (fun p j => p.send i m j) p by
    exact h (List.finRange n) p []
  intro l
  induction l with
  | nil => simp
  | cons j l ih => intro p acc; simp [ih]

theorem disseminate_view (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    (disseminate i p m).1.view = p.view := by
  rw [disseminate_fst]
  induction List.finRange n generalizing p with
  | nil => rfl
  | cons j l ih => rw [List.foldl_cons, ih, Processor.send_view]

theorem mem_S_send_or_signer (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n)
    {m' : Msg n Tx} (h : m' ∈ (p.send i m j).S) : m' ∈ p.S ∨ m' = m := by
  rw [Processor.send_S] at h
  split_ifs at h
  · exact (Finset.mem_insert.mp h).symm.imp_left id
  · exact Or.inl h

/-- 送った後の S にあるメッセージは、前からあったか、送ったもの。 -/
theorem mem_S_disseminate_or (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) {m' : Msg n Tx}
    (h : m' ∈ (disseminate i p m).1.S) : m' ∈ p.S ∨ m' = m := by
  rw [disseminate_fst] at h
  generalize List.finRange n = l at h
  induction l generalizing p with
  | nil => exact Or.inl h
  | cons j l ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h | h
    · exact mem_S_send_or_signer i p m j h
    · exact Or.inr h

/-! ### S の列挙
`Finset.toList` の順に並べる。論文が「辞書順最小」や「some b」で 1 つ選ぶ箇所は、
この順で先のものを取る。 -/

/-- S にある nullify の view を重複なく列挙する。 -/
noncomputable def nullifyViews (S : Finset (Msg n Tx)) : List View :=
  (S.toList.filterMap fun m => match m with | .nullify _ v => some v | _ => none).dedup

/-- S にある票のブロックを重複なく列挙する。 -/
noncomputable def votedBlocks (S : Finset (Msg n Tx)) : List (Block n Tx) :=
  (S.toList.filterMap fun m => match m with | .vote _ b => some b | _ => none).dedup

/-- S が含む、lead(v) の署名付きの view v のブロックを重複なく列挙する。 -/
noncomputable def proposals (lead : View → Fin n) (S : Finset (Msg n Tx)) (v : View) :
    List (Block n Tx) :=
  (S.toList.filterMap fun m => match m.block with
    | some b => if b.signer = some (lead v) ∧ b.view = v then some b else none
    | none => none).dedup

omit [DecidableEq Tx] in
theorem mem_nullifyViews {S : Finset (Msg n Tx)} {q : Fin n} {v : View} (h : Msg.nullify q v ∈ S) :
    v ∈ nullifyViews S := by
  simp only [nullifyViews, List.mem_dedup, List.mem_filterMap, Finset.mem_toList]
  exact ⟨Msg.nullify q v, h, rfl⟩

theorem mem_votedBlocks {S : Finset (Msg n Tx)} {q : Fin n} {b : Block n Tx}
    (h : Msg.vote q b ∈ S) : b ∈ votedBlocks S := by
  simp only [votedBlocks, List.mem_dedup, List.mem_filterMap, Finset.mem_toList]
  exact ⟨Msg.vote q b, h, rfl⟩

theorem exists_vote_of_mem_votedBlocks {S : Finset (Msg n Tx)} {b : Block n Tx}
    (h : b ∈ votedBlocks S) : ∃ q, Msg.vote q b ∈ S := by
  simp only [votedBlocks, List.mem_dedup, List.mem_filterMap, Finset.mem_toList] at h
  obtain ⟨m, hm, hmb⟩ := h
  cases m with
  | propose b' => simp at hmb
  | vote q b' => simp at hmb; subst hmb; exact ⟨q, hm⟩
  | nullify q v => simp at hmb
  | tx tr => simp at hmb

theorem containsBlock_of_mem_votedBlocks {S : Finset (Msg n Tx)} {b : Block n Tx}
    (h : b ∈ votedBlocks S) : containsBlock S b := by
  simp only [votedBlocks, List.mem_dedup, List.mem_filterMap, Finset.mem_toList] at h
  obtain ⟨m, hm, hmb⟩ := h
  refine ⟨m, hm, ?_⟩
  cases m with
  | vote q b' => simp only [Option.some.injEq] at hmb; subst hmb; rfl
  | _ => simp at hmb

theorem mem_votedBlocks_of_subset {S S' : Finset (Msg n Tx)} (h : S ⊆ S') {b : Block n Tx}
    (hb : b ∈ votedBlocks S) : b ∈ votedBlocks S' := by
  simp only [votedBlocks, List.mem_dedup, List.mem_filterMap, Finset.mem_toList] at hb ⊢
  obtain ⟨m, hm, hmb⟩ := hb
  exact ⟨m, h hm, hmb⟩

theorem containsBlock_of_mem_proposals {lead : View → Fin n} {S : Finset (Msg n Tx)} {v : View}
    {b : Block n Tx} (h : b ∈ proposals lead S v) : containsBlock S b := by
  simp only [proposals, List.mem_dedup, List.mem_filterMap, Finset.mem_toList] at h
  obtain ⟨m, hm, hmb⟩ := h
  refine ⟨m, hm, ?_⟩
  cases hb : m.block with
  | none => simp [hb] at hmb
  | some b' =>
    simp only [hb] at hmb
    split_ifs at hmb
    simp only [Option.some.injEq] at hmb; subst hmb; rfl

/-- S にある、M-notarisation を持つ view v のブロックを重複なく列挙する。 -/
noncomputable def mNotarisedAt (f : Nat) (S : Finset (Msg n Tx)) (v : View) :
    List (Block n Tx) :=
  (votedBlocks S).filter fun b => decide (b.view = v ∧ MNotarised f S b)

theorem mem_mNotarisedAt {f : Nat} {S : Finset (Msg n Tx)} {v : View} {b : Block n Tx}
    (h : b ∈ mNotarisedAt f S v) : b.view = v ∧ MNotarised f S b := by
  simp only [mNotarisedAt, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

theorem mem_votedBlocks_of_mem_mNotarisedAt {f : Nat} {S : Finset (Msg n Tx)} {v : View}
    {b : Block n Tx} (h : b ∈ mNotarisedAt f S v) : b ∈ votedBlocks S := by
  simp only [mNotarisedAt, List.mem_filter] at h
  exact h.1

theorem mem_mNotarisedAt_of {f : Nat} {S : Finset (Msg n Tx)} {b : Block n Tx}
    (hb : b ∈ votedBlocks S)
    (hM : MNotarised f S b) : b ∈ mNotarisedAt f S b.view := by
  simp only [mNotarisedAt, List.mem_filter, decide_eq_true_eq]
  exact ⟨hb, trivial, hM⟩

theorem containsBlock_of_mem_mNotarisedAt {f : Nat} {S : Finset (Msg n Tx)} {v : View}
    {b : Block n Tx} (h : b ∈ mNotarisedAt f S v) : containsBlock S b := by
  simp only [mNotarisedAt, List.mem_filter] at h
  exact containsBlock_of_mem_votedBlocks h.1

/-! ## 各部分
`Algo.step` の評価順に並べる。 -/

/-! ### 16〜21 行 -/

/-- S にあるメッセージが言及する view の最大 -/
noncomputable def maxView (S : Finset (Msg n Tx)) : Nat := S.sup fun m => m.view.val

/-- S に view v の証明書がある: v の nullification か、view v のブロックの M-notarisation。
    16 行と 19 行の条件。 -/
def HasCert (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Prop :=
  Nullified f S v ∨ mNotarisedAt f S v ≠ []

noncomputable instance (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Decidable (HasCert f S v) :=
  inferInstanceAs (Decidable (_ ∨ _))

omit [DecidableEq Tx] in
theorem view_le_maxView {S : Finset (Msg n Tx)} {m : Msg n Tx} (h : m ∈ S) :
    m.view.val ≤ maxView S :=
  Finset.le_sup (f := fun m => m.view.val) h

/-- nullification のある view は、S にあるメッセージの view を超えない。 -/
theorem view_le_maxView_of_nullified {f : Nat} {S : Finset (Msg n Tx)} {v : View}
    (h : Nullified f S v) : v.val ≤ maxView S := by
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos _) h)
  exact view_le_maxView (mem_nullifiers.mp hq)

/-- M-notarisation を持つブロックのある view は、S にあるメッセージの view を超えない。 -/
theorem view_le_maxView_of_mem_mNotarisedAt {f : Nat} {S : Finset (Msg n Tx)} {v : View}
    {b : Block n Tx} (hb : b ∈ mNotarisedAt f S v) : v.val ≤ maxView S := by
  obtain ⟨q, hq⟩ := exists_vote_of_mem_votedBlocks (mem_votedBlocks_of_mem_mNotarisedAt hb)
  have h1 : b.view.val ≤ maxView S := view_le_maxView hq
  rw [(mem_mNotarisedAt hb).1] at h1
  exact h1

/-- S にあるメッセージの view を超えない view のメッセージを送っても、`maxView` は増えない。 -/
theorem maxView_disseminate_le {i : Fin n} {p : Processor n Tx} {m : Msg n Tx}
    (hm : m.view.val ≤ maxView p.S) : maxView (disseminate i p m).1.S ≤ maxView p.S := by
  apply Finset.sup_le
  intro m' hm'
  rcases mem_S_disseminate_or i p m hm' with h | rfl
  · exact view_le_maxView h
  · exact hm

/-- 19〜21 行で、投票するかしないかしてから次の view へ進んだ後の尺度は、進む前より小さい。 -/
theorem measure_lt_of_mem_mNotarisedAt {f : Nat} {i : Fin n} {p : Processor n Tx} {b : Block n Tx}
    (hb : b ∈ mNotarisedAt f p.S p.view) :
    maxView (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
        else (p, [])).1.progress.S + 1
      - (if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
        else (p, [])).1.progress.view.val
      < maxView p.S + 1 - p.view.val := by
  have h1 := view_le_maxView_of_mem_mNotarisedAt hb
  have hbv := (mem_mNotarisedAt hb).1
  split_ifs
  · have h2 : maxView (disseminate i p (.vote i b)).1.S ≤ maxView p.S :=
      maxView_disseminate_le (by show b.view.val ≤ maxView p.S; rw [hbv]; exact h1)
    show maxView (disseminate i p (.vote i b)).1.S + 1
      - ((disseminate i p (.vote i b)).1.view.val + 1) < maxView p.S + 1 - p.view.val
    rw [disseminate_view]; omega
  · show maxView p.S + 1 - (p.view.val + 1) < maxView p.S + 1 - p.view.val
    omega

/-- 16〜21 行。現在の view の nullification があれば次の view へ進む（16〜17 行）。なければ、
    現在の view のブロックの M-notarisation があれば、未投票で nullify も送っていなければ
    そのブロックに投票し、次の view へ進む（19〜21 行）。複数あれば `mNotarisedAt` の順で先の
    ブロックに投票する。進んだら新しい view で繰り返す。 -/
noncomputable def climb (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if Nullified f p.S p.view then
    let r := climb f i p.progress
    (r.1, Action.progress :: r.2)
  else if hM : mNotarisedAt f p.S p.view ≠ [] then
    let b := (mNotarisedAt f p.S p.view).head hM
    let r :=
      if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b) else (p, [])
    let r' := climb f i r.1.progress
    (r'.1, r.2 ++ Action.progress :: r'.2)
  else (p, [])
termination_by maxView p.S + 1 - p.view.val
decreasing_by
  · rename_i hN
    have h1 := view_le_maxView_of_nullified hN
    show maxView p.S + 1 - (p.view.val + 1) < maxView p.S + 1 - p.view.val
    omega
  · exact measure_lt_of_mem_mNotarisedAt (List.head_mem hM)

theorem climb_of_nullified {f : Nat} (i : Fin n) {p : Processor n Tx}
    (hN : Nullified f p.S p.view) :
    climb f i p = ((climb f i p.progress).1, Action.progress :: (climb f i p.progress).2) := by
  conv_lhs => rw [climb]
  rw [if_pos hN]

theorem climb_of_mnotarised {f : Nat} (i : Fin n) {p : Processor n Tx}
    (hN : ¬ Nullified f p.S p.view) (hM : mNotarisedAt f p.S p.view ≠ []) :
    climb f i p
      = let r := if p.notarised = none ∧ p.nullified = false
          then disseminate i p (.vote i ((mNotarisedAt f p.S p.view).head hM)) else (p, [])
        ((climb f i r.1.progress).1, r.2 ++ Action.progress :: (climb f i r.1.progress).2) := by
  conv_lhs => rw [climb]
  rw [if_neg hN, dif_pos hM]

theorem climb_of_not {f : Nat} (i : Fin n) {p : Processor n Tx} (hc : ¬ HasCert f p.S p.view) :
    climb f i p = (p, []) := by
  have hN : ¬ Nullified f p.S p.view := fun h => hc (Or.inl h)
  have hM : ¬ mNotarisedAt f p.S p.view ≠ [] := fun h => hc (Or.inr h)
  conv_lhs => rw [climb]
  rw [if_neg hN, dif_neg hM]

/-- `climb` の再帰に沿った帰納法: 16〜17 行で進む場合、19〜21 行で進む場合、止まる場合。 -/
@[elab_as_elim]
theorem climb_induction (f : Nat) (i : Fin n) {motive : Processor n Tx → Prop}
    (nullified : ∀ p, Nullified f p.S p.view → motive p.progress → motive p)
    (mnotarised : ∀ p, ¬ Nullified f p.S p.view → ∀ hM : mNotarisedAt f p.S p.view ≠ [],
      motive (if p.notarised = none ∧ p.nullified = false
        then disseminate i p (.vote i ((mNotarisedAt f p.S p.view).head hM))
        else (p, [])).1.progress → motive p)
    (quiescent : ∀ p, ¬ Nullified f p.S p.view → ¬ mNotarisedAt f p.S p.view ≠ [] → motive p)
    (p : Processor n Tx) : motive p := by
  refine climb.induct f i motive nullified ?_ quiescent p
  intro p hN hM
  dsimp only
  simp only [dite_eq_ite]
  exact mnotarised p hN hM

/-! ### 5〜7 行（SelectParent と ProposeChild） -/

/-- SelectParent(S, v)（§4）: M-notarisation を持つ view v 未満のブロックのうち、view が
    最大のもの。票のあるブロックに候補が無ければ genesis。同じ view に複数あれば `votedBlocks`
    の順で先のもの。 -/
noncomputable def selectParent (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Block n Tx :=
  (((votedBlocks S).filter fun b => decide (b.view.val < v.val ∧ MNotarised f S b)).argmax
    fun b => b.view.val).getD .gen

open Classical in
/-- ProposeChild の Tr（§4）: 受信済みの取引のうち、S が含む b の祖先の Tr に無いもの。 -/
noncomputable def payload (S : Finset (Msg n Tx)) (b : Block n Tx) : List Tx :=
  (S.toList.filterMap fun m => match m with | .tx tr => some tr | _ => none).filter
    fun tr => decide (∀ a, Block.Ancestor a b → containsBlock S a → tr ∉ a.tr)

/-- 5〜7 行。リーダーで未提案なら、SelectParent の子を ProposeChild で作って全員へ送る。 -/
noncomputable def propose (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if lead p.view = i ∧ p.proposed = false then
    let parent := selectParent f p.S p.view
    disseminate i p (.propose (.node i p.view (payload p.S parent) parent))
  else (p, [])

/-! ### 9〜11 行 -/

open Classical in
/-- 9〜11 行。S にある lead(v) の view v の提案が 1 つで valid proposal なら、未投票で nullify も
    送っていなければ投票する。`ValidProposal` の判定に古典論理を使う。 -/
noncomputable def voteProposal (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  match proposals lead p.S p.view with
  | [b] =>
    if ValidProposal f lead p.S p.view b ∧ p.notarised = none ∧ p.nullified = false then
      disseminate i p (.vote i b)
    else (p, [])
  | _ => (p, [])

/-! ### 13〜14 行 -/

/-- 13〜14 行。T = 2Δ で、nullify も票も送っていなければ nullify(v) を全員へ送る。 -/
def nullifyTimeout (Δ : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if p.timer = 2 * Δ ∧ p.nullified = false ∧ p.notarised = none then
    disseminate i p (.nullify i p.view)
  else (p, [])

/-! ### 24〜28 行 -/

open Classical in
/-- 24〜28 行。nullify を送っておらず、投票済みで、proof of no progress があれば nullify(v) を
    全員へ送る。 -/
noncomputable def nullifyNoProgress (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if p.nullified = false ∧ p.notarised ≠ none ∧ NoProgress f p.S p.view p.notarised then
    disseminate i p (.nullify i p.view)
  else (p, [])

/-! ### 2〜3 行と §4 の取引転送 -/

/-- S にある nullify(v) の署名者のうち、番号の小さい順に 2f + 1 人。論文の「辞書順最小の
    nullification」の署名者。 -/
def leastNullifiers (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Finset (Fin n) :=
  (((nullifiers S v).sort (· ≤ ·)).take (2 * f + 1)).toFinset

/-- S にある b への票の署名者のうち、番号の小さい順に 2f + 1 人。論文の「辞書順最小の
    M-notarisation」の署名者。 -/
def leastVoters (f : Nat) (S : Finset (Msg n Tx)) (b : Block n Tx) : Finset (Fin n) :=
  (((voters S b).sort (· ≤ ·)).take (2 * f + 1)).toFinset

/-- 新しく受け取ったものを全員へ送る: nullification（2 行）、M-notarisation（3 行）、
    取引（§4 本文）。new（§4）とは、S にあって prevS にないこと。証明書は、署名者の番号が小さい順に
    2f + 1 人分のメッセージを送る。 -/
noncomputable def forwardNew (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  let nulls := (nullifyViews p.S).filter fun v =>
    decide (Nullified f p.S v ∧ ¬ Nullified f p.prevS v)
  let notas := (votedBlocks p.S).filter fun b =>
    decide (MNotarised f p.S b ∧ ¬ MNotarised f p.prevS b)
  let ms :=
    (nulls.flatMap fun v => (leastNullifiers f p.S v).toList.map fun q => Msg.nullify q v)
    ++ (notas.flatMap fun b => (leastVoters f p.S b).toList.map fun q => Msg.vote q b)
    ++ (p.S.toList.filter fun m => match m with | .tx _ => decide (m ∉ p.prevS) | _ => false)
  disseminateAll i p ms

/-! ## Algorithm 1 -/

/-- Algorithm 1: p_i が 1 スロットで起こす動作の列。16〜21 行、5〜7 行、9〜11 行、13〜14 行、
    24〜28 行、2〜3 行の順に各部分を評価し、各部分が返す局所状態を次の部分に渡す。 -/
noncomputable def step (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    List (Action n Tx) :=
  let r₁ := climb f i p
  let r₂ := propose f lead i r₁.1
  let r₃ := voteProposal f lead i r₂.1
  let r₄ := nullifyTimeout Δ i r₃.1
  let r₅ := nullifyNoProgress f i r₄.1
  let r₆ := forwardNew f i r₅.1
  r₁.2 ++ r₂.2 ++ r₃.2 ++ r₄.2 ++ r₅.2 ++ r₆.2

end Algo

end Minimmit
