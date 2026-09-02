import Minimmit.Model.Certificate
import Mathlib.Data.List.MinMax

/-!
# Algorithm 1

局所状態から 1 スロット分の動作の列を返す関数 `Algo.step` と、その部品。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type} [DecidableEq Tx]

namespace Algo

/-! ### 送信の局所効果
動作の列を組み立てながら、`Processor.send` で局所状態にも同じ効果を与える。 -/

/-- m を全員へ送る（disseminate）。自分宛も含み、`Processor.send` が即時受信にする。 -/
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

/-- S にある nullify message の view（重複なし）。 -/
noncomputable def nullifyViews (S : Finset (Msg n Tx)) : List View :=
  (S.toList.filterMap fun m => match m with | .nullify _ v => some v | _ => none).dedup

/-- S にある票のブロック（重複なし）。 -/
noncomputable def votedBlocks (S : Finset (Msg n Tx)) : List (Block Tx) :=
  (S.toList.filterMap fun m => match m with | .vote _ b => some b | _ => none).dedup

/-- S にある、lead(v) の署名付きの view v のブロック（重複なし）。valid proposal の (i) は
    これがちょうど 1 つであること。 -/
noncomputable def proposals (lead : View → Fin n) (S : Finset (Msg n Tx)) (v : View) :
    List (Block Tx) :=
  (S.toList.filterMap fun m => match m with
    | .block q b => if q = lead v ∧ b.view = v then some b else none
    | _ => none).dedup

/-- S にある、M-notarisation を持つ view v のブロック（重複なし）。 -/
noncomputable def mNotarisedAt (f : Nat) (S : Finset (Msg n Tx)) (v : View) :
    List (Block Tx) :=
  (votedBlocks S).filter fun b => decide (b.view = v ∧ MNotarised f S b)

/-! ### 2〜3 行と §4 の取引転送 -/

/-- 新しく受け取ったものを全員へ送る: nullification（2 行）、M-notarisation（3 行）、
    取引（§4 本文）。新しい = S に含まれ prevS に含まれない。prevS は前スロット冒頭の S
    なので、前スロットに自分の送信で完成した証明書もここで送る。

    証明書は、それを構成する message を S にある分だけ全部送る。論文は「new」の第 2 条件で
    辞書順最小の 2f + 1 個を 1 つ選んで送る（§4）。§5 の証明が転送に使うのは「新しい証明書を
    受け取った正直者は全員へ送る」ことだけで、全部送っても各宛先が受け取る集合は論文の
    上位集合になる。差が出るのは §6.4 の通信量の見積もりで、これは形式化していない。 -/
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

/-! ### 5〜7 行（SelectParent と ProposeChild） -/

/-- SelectParent(S, v)（§4）: M-notarisation を持つ view v 未満のブロックのうち、view が
    最大のもの。票のあるブロックに候補が無ければ genesis（view 0 で常に M-notarisation を
    持つ）。論文の「辞書順最小」の代わりに、同じ view に複数あれば `votedBlocks` の順で
    先のもの。 -/
noncomputable def selectParent (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Block Tx :=
  (((votedBlocks S).filter fun b => decide (b.view.val < v.val ∧ MNotarised f S b)).argmax
    fun b => b.view.val).getD .gen

/-- ProposeChild(b, v) の Tr（§4）: 受信済みで b の祖先に含まれない取引。 -/
noncomputable def payload (S : Finset (Msg n Tx)) (b : Block Tx) : List Tx :=
  (S.toList.filterMap fun m => match m with | .tx tr => some tr | _ => none).filter
    fun tr => decide (tr ∉ b.trStar)

/-! ### Algorithm 1 -/

open Classical in
/-- Algorithm 1: p_i が 1 スロットで起こす動作の列。行の順に局所状態を更新しながら決める。
    `ValidProposal` の判定に古典論理を使う。31〜32 行の Finalise は動作を伴わないので無く、
    finalise したことは S に L-notarisation があることで表す。 -/
noncomputable def step (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
    List (Action n Tx) :=
  -- 2〜3 行
  let r₁ := forwardNew f i p
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
  -- 16〜17 行
  let r₅ : Processor n Tx × List (Action n Tx) :=
    if Nullified f p.S p.view then (p.progress, [Action.progress]) else (p, [])
  let p := r₅.1
  -- 19〜21 行。複数あれば `mNotarisedAt` の順で先のブロックに投票する
  let r₆ : Processor n Tx × List (Action n Tx) :=
    match mNotarisedAt f p.S p.view with
    | b :: _ =>
      let r :=
        if p.notarised = none ∧ p.nullified = false then disseminate i p (.vote i b)
        else (p, [])
      (r.1.progress, r.2 ++ [Action.progress])
    | [] => (p, [])
  let p := r₆.1
  -- 24〜28 行
  let r₇ :=
    if p.nullified = false ∧ p.notarised ≠ none ∧ NoProgress f p.S p.view p.notarised then
      disseminate i p (.nullify i p.view)
    else (p, [])
  r₁.2 ++ r₂.2 ++ r₃.2 ++ r₄.2 ++ r₅.2 ++ r₆.2 ++ r₇.2

end Algo

end Minimmit
