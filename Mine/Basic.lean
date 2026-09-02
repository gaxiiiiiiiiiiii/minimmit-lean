import Mathlib.Data.Finset.Card

/-!
# Minimmit の形式化

論文 arXiv:2508.10862 に基づく。
-/

namespace Mine

/-- view 番号（genesis のみ 0）。`Time` とは別の型。 -/
structure View where
  val : Nat
deriving DecidableEq

/-- タイムスロット。 -/
structure Time where
  val : Nat
deriving DecidableEq

instance : Coe View Nat := ⟨View.val⟩
instance : Coe Time Nat := ⟨Time.val⟩

variable {Tx : Type}

/-- ブロック（§4.2）: genesis か、(view, 取引列, 親) の組。親はハッシュ値
    でなく親ブロックそのもの。取引列が相異なることは型に含まない。 -/
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

/-- メッセージ（§4.2）: 提案・票・nullify は署名者 q を持つ。取引（§2）は
    環境の署名を持たず、Tx 型の値はすべて取引として扱う。 -/
inductive Msg (n : Nat) (Tx : Type) : Type where
  | block (q : Fin n) (b : Block Tx) : Msg n Tx
  | vote (q : Fin n) (b : Block Tx) : Msg n Tx
  | nullify (q : Fin n) (v : View) : Msg n Tx
  | tx (tr : Tx) : Msg n Tx

/-- 署名者。取引は環境の署名なので none。 -/
def Msg.signer {n : Nat} : Msg n Tx → Option (Fin n)
  | .block q _   => some q
  | .vote q _    => some q
  | .nullify q _ => some q
  | .tx _        => none

/-- プロセッサの局所状態（§4.3, Table 2）。自分の添字は持たない。 -/
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

/-- 網に載る単位: どのメッセージが、誰宛に、いつ送られたか。 -/
structure Packet (n : Nat) (Tx : Type) where
  msg : Msg n Tx
  dst : Fin n
  sentAt : Time

/-- 大域状態: 全プロセッサの局所状態、腐敗集合、網に載った packet、現在のタイムスロット。 -/
structure State (n : Nat) (Tx : Type) where
  /-- 各プロセッサ。`procs i` が p_i。 -/
  procs : Fin n → Processor n Tx
  /-- これまでに腐敗したプロセッサ。 -/
  byz : Finset (Fin n)
  /-- 網に載った packet の全体。 -/
  pool : Set (Packet n Tx)
  /-- 現在のタイムスロット。`State.tick` で進む。 -/
  now : Time


namespace Processor

variable {n : Nat}

/-! ### 自動遷移
単独では起こらない遷移。動きかスロットに付随して呼ばれる。 -/

/-- 受信: S に m を入れる。到着と、自分の送信の即時受信（§4 冒頭）の両方が
    ここを通る。 -/
def receive (p : Processor n Tx) (m : Msg n Tx) : Processor n Tx :=
  { p with S := insert m p.S }

/-- タイマー T を 1 進める（スロットごと）。 -/
def tick (p : Processor n Tx) : Processor n Tx :=
  { p with timer := p.timer + 1 }

/-- m を j へ送った結果の局所状態への効果。`State.send` に付随する。m が自分の
    署名付きなら種類に応じてフラグを立てる（§4「自分が既に何を送ったかを記録する」。
    他人のものと取引では何もしない）。j が自分なら即時受信。 -/
def send (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n) :
    Processor n Tx :=
  let p := match m with
    | .block q _   => if q = i then { p with proposed := true } else p
    | .vote q b    => if q = i then { p with notarised := some b } else p
    | .nullify q _ => if q = i then { p with nullified := true } else p
    | .tx _        => p
  if j = i then p.receive m else p

/-! ### 動き
タイミングが入力になる遷移。 -/

/-- 次の view へ（2 つの前進が共有するリセット）: v := v + 1、T := 0、
    nullified・proposed := false、notarised := ⊥。S は触らない。 -/
def progress (p : Processor n Tx) : Processor n Tx :=
  { p with view := ⟨p.view.val + 1⟩, timer := 0,
           nullified := false, proposed := false, notarised := none }

end Processor

namespace State

variable {n : Nat}

/-! ### 自動遷移
単独では起こらない遷移、または配管。 -/

/-- procs i だけを f で置き換える（配管）。 -/
def update (s : State n Tx) (i : Fin n) (f : Processor n Tx → Processor n Tx) :
    State n Tx :=
  { s with procs := Function.update s.procs i (f (s.procs i)) }

/-- packet x を網に載せる。send に付随する自動遷移。 -/
def transmit (s : State n Tx) (x : Packet n Tx) : State n Tx :=
  { s with pool := insert x s.pool }

/-- スロットを進める: 全プロセッサの `tick` と now + 1。 -/
def tick (s : State n Tx) : State n Tx :=
  { s with procs := fun i => (s.procs i).tick, now := ⟨s.now.val + 1⟩ }

/-! ### 入力
タイミングが入力になる遷移。 -/

/-- p_i が m を j へ送る。m は自分の署名付きか、受信済みのもの。局所状態への
    効果は `Processor.send`、網には now 付きの packet。 -/
def send (s : State n Tx) (i : Fin n) (m : Msg n Tx) (j : Fin n)
    (_h : m.signer = some i ∨ m ∈ (s.procs i).S) : State n Tx :=
  (s.update i (·.send i m j)).transmit ⟨m, j, s.now⟩

/-- p_i が次の view へ。 -/
def progress (s : State n Tx) (i : Fin n) : State n Tx :=
  s.update i Processor.progress

/-- pool にある packet x のメッセージが宛先に届く。 -/
def deliver (s : State n Tx) (x : Packet n Tx) (_hx : x ∈ s.pool) : State n Tx :=
  s.update x.dst (·.receive x.msg)

/-- 環境が p_j に取引 tr を渡す。 -/
def submit (s : State n Tx) (j : Fin n) (tr : Tx) : State n Tx :=
  s.update j (·.receive (.tx tr))

/-- p_i が腐敗する。 -/
def corrupt (s : State n Tx) (i : Fin n) : State n Tx :=
  { s with byz := insert i s.byz }

end State

end Mine
