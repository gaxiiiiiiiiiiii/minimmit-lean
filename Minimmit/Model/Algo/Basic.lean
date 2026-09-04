import Minimmit.Model.Certificate.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Algorithm 1

局所状態から 1 スロット分の動作の列を返す関数 `Algo.step` と、その部品。`step` の各段は
Algo/Stage で `forwardMsgs`・`propose`・`voteProposal`・`nullifyTimeout`・`advanceM`・
`nullifyNoProgress` として切り出してあり、`step` との一致は `step_eq_stepPair`。補題は段の
名前で述べる。`step` が送る message が遷移系の送信ガードを通ることは Timing の `Algo.send_guard`。

## 論文からの差異

- 評価順。論文の Algorithm 1 は各スロットで 2〜32 行を上から 1 回評価する。`step` は
  16〜21、5〜7、9〜11、13〜14、24〜28、2〜3 行の順に評価する。論文の Lemma 5.6 以降の
  時間の議論は、view に入った時点で提案し、証明書が届いた時点で転送することを使う。
  論文の行順では、view に入ったスロットで提案できず、そのスロットで完成した証明書を同じ
  スロットで転送できないので、これが 1〜2 スロット遅れる。行順でも論文の O(·) の主張は
  偽にならず、ずれは定数だが、証明の時間計算は書いてあるとおりには通らない。この評価順では
  通る。行順は擬似コードにしかなく、§3 の地の文は「Upon entering view v, p_i finds the
  greatest v′ < v …」「proceeds to view v + 1 immediately upon seeing an M-notarisation」と
  事象駆動で、この評価順はその順に当たる。
- 登り切り。16〜21 行は `climb` で、現在の view の証明書がある限り繰り返す。論文の
  Lemma 5.6 の証明と付録の Lemma E.6 は「最初の正直者が t に view v に入れば、全正直者は
  t + Δ までに v に入る」と主張するが、1 回評価では 1 スロットに高々 2 view しか進めず、
  GST 前に配送が遅れて証明書が一括で届く正直者について偽になる。繰り返す動作では
  `enter_all` として成り立ち、論文の議論がそのまま通る。§6.1 の「view を飛ばす」最適化は
  同じ穴を塞ぐもので、ここでは飛ばさず 1 view ずつ登る。§6.1 が追加する 2 つの規則は、順に
  登れば別の規則なしに満たされる。通過した view の M-notarised ブロックへ投票する規則は、
  `advanceOnce` が通過する各 view で 19〜20 行を評価することに当たる。リーダーが提案前に
  親の M-notarisation と間の view の nullification を待つ規則は、順に登れば view v に入った
  時点で揃っている（`leader_parent_mnotarised_all`・`leader_gaps_nullified_all`）。
- 転送。2〜3 行の転送 `forwardNew` は、新しい証明書を構成する message を S にある分すべて
  送る。論文は辞書順最小の 2f + 1 個を 1 組選ぶ。§5 の証明が転送に使うのは「新しい証明書を
  受け取った正直者は全員へ送る」ことだけで、すべて送っても各宛先が受け取る集合は論文の
  上位集合になる。差が出るのは通信量で、これは形式化していない。§6.4 が閾値署名で証明書を
  1 つの署名にまとめると、どの票を送るかの差は消える。
- 同点の選択。論文が「辞書順最小」や「some b」で 1 つ選ぶ箇所は、S を `Finset.toList` で
  並べた順で先のものを取る。論文の証明は選択の仕方を使わないので、この選択はその一例。
- finalise。31〜32 行の Finalise は動作を伴わないので `step` に無く、finalise したことは
  S に L-notarisation があることで表す。これは 31 行の条件そのもの。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

/-! ## 部品 -/

/-! ### 送信
動作の列を組み立てながら、`Processor.send` で局所状態にも同じ効果を与える。 -/

/-- m を全員へ送る。自分宛も含み、`Processor.send` が即時受信にする。 -/
def disseminate (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) :
    Processor n Tx × List (Action n Tx) :=
  (List.finRange n).foldl
    (fun (pa : Processor n Tx × List (Action n Tx)) j =>
      (pa.1.send i m j, pa.2 ++ [Action.send m j]))
    (p, [])

/-- ms の各 message を順に全員へ送る。 -/
def disseminateAll (i : Fin n) (p : Processor n Tx) (ms : List (Msg n Tx)) :
    Processor n Tx × List (Action n Tx) :=
  ms.foldl
    (fun (pa : Processor n Tx × List (Action n Tx)) m =>
      let r := disseminate i pa.1 m
      (r.1, pa.2 ++ r.2))
    (p, [])

/-! ### S の列挙
`Finset.toList` の順に並べる。論文が「辞書順最小」や「some b」で 1 つ選ぶ箇所は、
この順で先のものを取る。 -/

/-- S にある nullify の view を重複なく列挙する。 -/
noncomputable def nullifyViews (S : Finset (Msg n Tx)) : List View :=
  (S.toList.filterMap fun m => match m with | .nullify _ v => some v | _ => none).dedup

/-- S にある票のブロックを重複なく列挙する。 -/
noncomputable def votedBlocks (S : Finset (Msg n Tx)) : List (Block Tx) :=
  (S.toList.filterMap fun m => match m with | .vote _ b => some b | _ => none).dedup

/-- S にある、lead(v) の署名付きの view v のブロックを重複なく列挙する。valid proposal の
    条件 (i) は、これがちょうど 1 つであること。 -/
noncomputable def proposals (lead : View → Fin n) (S : Finset (Msg n Tx)) (v : View) :
    List (Block Tx) :=
  (S.toList.filterMap fun m => match m with
    | .block q b => if q = lead v ∧ b.view = v then some b else none
    | _ => none).dedup

/-- S にある、M-notarisation を持つ view v のブロックを重複なく列挙する。 -/
noncomputable def mNotarisedAt (f : Nat) (S : Finset (Msg n Tx)) (v : View) :
    List (Block Tx) :=
  (votedBlocks S).filter fun b => decide (b.view = v ∧ MNotarised f S b)

/-! ## 各段の部品
`step` の評価順に並べる。13〜14 行と 24〜28 行は部品を持たず、`step` に直接書く。 -/

/-! ### 16〜21 行 -/

/-- S にある message が言及する view の最大 -/
noncomputable def maxView (S : Finset (Msg n Tx)) : Nat := S.sup Msg.viewNum

/-- S に view v の証明書がある: v の nullification か、view v のブロックの M-notarisation。
    16 行と 19 行の条件。 -/
def HasCert (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Prop :=
  Nullified f S v ∨ mNotarisedAt f S v ≠ []

noncomputable instance (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Decidable (HasCert f S v) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- 16〜21 行を 1 回評価する。現在の view の nullification があれば進む（16〜17 行）。
    なければ、現在の view のブロックの M-notarisation があれば、未投票なら投票してから進む
    （19〜21 行）。複数あれば `mNotarisedAt` の順で先のブロックに投票する。 -/
noncomputable def advanceOnce (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  if Nullified f p.S p.view then (p.progress, [Action.progress])
  else
    match mNotarisedAt f p.S p.view with
    | b :: _ =>
      let r :=
        if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
        else (p, [])
      (r.1.progress, r.2 ++ [Action.progress])
    | [] => (p, [])

/-- 現在の view の証明書がある限り `advanceOnce` を繰り返す。fuel 回で打ち切る。 -/
noncomputable def climb (f : Nat) (i : Fin n) :
    Nat → Processor n Tx → Processor n Tx × List (Action n Tx)
  | 0, p => (p, [])
  | fuel + 1, p =>
    if HasCert f p.S p.view then
      let r := advanceOnce f i p
      let r' := climb f i fuel r.1
      (r'.1, r.2 ++ r'.2)
    else (p, [])

/-! ### 5〜7 行（SelectParent と ProposeChild） -/

/-- SelectParent(S, v)（§4）: M-notarisation を持つ view v 未満のブロックのうち、view が
    最大のもの。票のあるブロックに候補が無ければ genesis。genesis は view 0 で常に
    M-notarisation を持つ。同じ view に複数あれば `votedBlocks` の順で先のもの。 -/
noncomputable def selectParent (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Block Tx :=
  (((votedBlocks S).filter fun b => decide (b.view.val < v.val ∧ MNotarised f S b)).argmax
    fun b => b.view.val).getD .gen

/-- ProposeChild(b, v) の Tr（§4）: 受信済みで b の祖先に含まれない取引。 -/
noncomputable def payload (S : Finset (Msg n Tx)) (b : Block Tx) : List Tx :=
  (S.toList.filterMap fun m => match m with | .tx tr => some tr | _ => none).filter
    fun tr => decide (tr ∉ b.trStar)

/-! ### 2〜3 行と §4 の取引転送 -/

/-- 新しく受け取ったものを全員へ送る: nullification（2 行）、M-notarisation（3 行）、
    取引（§4 本文）。「新しい」とは、S にあって prevS にないこと。スロットの最後に評価する
    ので、このスロットで届いたものと自分の送信で完成した証明書をこのスロットで送る。
    その証明書での view 前進は、16〜21 行をスロットの最初に評価するので次のスロット。
    証明書は、それを構成する message を S にある分だけ全部送る。 -/
noncomputable def forwardNew (f : Nat) (i : Fin n) (p : Processor n Tx) :
    Processor n Tx × List (Action n Tx) :=
  let nulls := (nullifyViews p.S).filter fun v =>
    decide (Nullified f p.S v ∧ ¬ Nullified f p.prevS v)
  let notas := (votedBlocks p.S).filter fun b =>
    decide (MNotarised f p.S b ∧ ¬ MNotarised f p.prevS b)
  let ms :=
    (nulls.flatMap fun v => p.S.toList.filter fun m => decide (∃ q, m = Msg.nullify q v))
    ++ (notas.flatMap fun b => p.S.toList.filter fun m => decide (∃ q, m = Msg.vote q b))
    ++ (p.S.toList.filter fun m => match m with | .tx _ => decide (m ∉ p.prevS) | _ => false)
  disseminateAll i p ms

/-! ## Algorithm 1 -/

open Classical in
/-- Algorithm 1: p_i が 1 スロットで起こす動作の列。16〜21、5〜7、9〜11、13〜14、24〜28、
    2〜3 行の順に評価し、局所状態を更新しながら決める。`ValidProposal` の判定に古典論理を
    使う。 -/
noncomputable def step (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    List (Action n Tx) :=
  -- 16〜21 行。証明書のある view は S にある message の view を超えないので、
  -- maxView p.S + 1 回で止まる
  let r₁ := climb f i (maxView p.S + 1) p
  let p := r₁.1
  -- 5〜7 行
  let r₂ :=
    if lead p.view = i ∧ p.proposed = false then
      let parent := selectParent f p.S p.view
      disseminate i p (.block i (.node p.view (payload p.S parent) parent))
    else (p, [])
  let p := r₂.1
  -- 9〜11 行
  let r₃ :=
    match proposals lead p.S p.view with
    | [b] =>
      if ValidProposal f lead p.S p.view b ∧ p.notarised = none ∧ p.nullified = false then
        disseminate i p (.vote i b)
      else (p, [])
    | _ => (p, [])
  let p := r₃.1
  -- 13〜14 行
  let r₄ :=
    if p.timer = 2 * Δ ∧ p.nullified = false ∧ p.notarised = none then
      disseminate i p (.nullify i p.view)
    else (p, [])
  let p := r₄.1
  -- 24〜28 行
  let r₅ :=
    if p.nullified = false ∧ p.notarised ≠ none ∧ NoProgress f p.S p.view p.notarised then
      disseminate i p (.nullify i p.view)
    else (p, [])
  let p := r₅.1
  -- 2〜3 行
  let r₆ := forwardNew f i p
  r₁.2 ++ r₂.2 ++ r₃.2 ++ r₄.2 ++ r₅.2 ++ r₆.2

end Algo

end Minimmit
