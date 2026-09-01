import Mathlib.Data.Finset.Card

/-!
# Minimmit 再形式化

論文 arXiv:2508.10862 準拠。本家 `Minimmit/` とは独立。
-/

namespace Mine

/-- view 番号（genesis のみ 0）。newtype で `Time` と型レベルに区別する。
    順序・算術は `.val`（ℕ）側で書き、omega を素で使う。View 上の
    順序・加算のインスタンスは置かない（必要になったら後付け）。 -/
structure View where
  val : Nat
deriving DecidableEq

/-- タイムスロット。扱いは `View` と同じ。 -/
structure Time where
  val : Nat
deriving DecidableEq

instance : Coe View Nat := ⟨View.val⟩
instance : Coe Time Nat := ⟨Time.val⟩

variable {Tx : Type}

/-- ブロック（§4.2）: genesis か、(view, 取引列, 親) の組。ハッシュは
    理想化し、親参照そのものを持つ（本家踏襲。仮定を満たすハッシュ関数
    による実装との整合は事後課題）。「相異なる取引の列」の相異なる性は
    型に入れず、有効性の条件に回す。 -/
inductive Block (Tx : Type) : Type where
  | gen : Block Tx
  | node (v : View) (tr : List Tx) (parent : Block Tx) : Block Tx

/-- `b.view`。genesis は 0。 -/
def Block.view : Block Tx → View
  | .gen => ⟨0⟩
  | .node v _ _ => v

/-- `b.Tr`。genesis は空。 -/
def Block.tr : Block Tx → List Tx
  | .gen => []
  | .node _ tr _ => tr

/-- `b.Tr*`（§2）: b と全祖先の payload を古い順に連結した列。 -/
def Block.trStar : Block Tx → List Tx
  | .gen => []
  | .node _ tr parent => parent.trStar ++ tr

/-- メッセージ（§4.2）: 提案・票・nullify は署名者 q を埋め込んで持つ
    （理想化署名 = 剥がせない署名者タグ）。取引は §2 の「環境が署名した
    特別な形のメッセージ」だが、環境署名は理想化して持たない — Tx 型の
    値はすべて有効な取引として扱う。 -/
inductive Msg (n : Nat) (Tx : Type) : Type where
  | block (q : Fin n) (b : Block Tx) : Msg n Tx
  | vote (q : Fin n) (b : Block Tx) : Msg n Tx
  | nullify (q : Fin n) (v : View) : Msg n Tx
  | tx (tr : Tx) : Msg n Tx

/-- プロセッサ（§4.3, Table 2）: 局所変数の全部。自分の添字 i は
    フィールドに持たず、スロット遷移が引数として受け取る
    （5 行目のガード p_i = lead(v) はそこで読む）。 -/
structure Processor (n : Nat) (Tx : Type) where
  /-- 現在の view。初期値 1。 -/
  view : View
  /-- タイマー T。view 入場で 0 にリセット、スロットごとに +1。 -/
  timer : Nat
  /-- この view で nullify(v) を送ったか。 -/
  nullified : Bool
  /-- この view で提案したか。 -/
  proposed : Bool
  /-- この view で投票したブロック。⊥ = `none`。 -/
  notarised : Option (Block Tx)
  /-- 受信メッセージ全集合。 -/
  S : Set (Msg n Tx)

/-- 送信の記録: どのメッセージが、誰から誰へ、いつ送られたか。
    `sender` は送り手であって `msg` に埋め込まれた署名者とは限らない
    （他人の署名済みメッセージの再送 = 証明書の転送）。 -/
structure Sent (n : Nat) (Tx : Type) where
  msg : Msg n Tx
  sender : Fin n
  recipient : Fin n
  sentAt : Time

/-- 大域状態: あるタイムスロットのシステム全体のスナップショット。
    時刻は持たない（実行 = State の列の添字が担う）。GST・Δ も実行を
    通じて不変の定数なので、フィールドでなくステップ関係の引数に回す。
    リーダー割り当ては §4.4 の固定輪番なので、状態ですらなくただの関数。 -/
structure State (n : Nat) (Tx : Type) where
  /-- 各プロセッサ。`procs i` が p_i。 -/
  procs : Fin n → Processor n Tx
  /-- これまでに腐敗したプロセッサ。ステップで単調増加し、濃度 ≤ f は
      実行の条件として課す。correct = 実行全体で一度もここに入らないこと。 -/
  byz : Finset (Fin n)
  /-- 送信プール: 送信の記録の全体。配送はここからしか起きない（真正性）。
      配送期限 max{GST, sentAt} + Δ はステップ関係が課す。 -/
  pool : Set (Sent n Tx)

end Mine
