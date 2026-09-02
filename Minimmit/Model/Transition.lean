import Mathlib.Data.Finset.Card

/-!
# 遷移系

§2・§4 の型（View・Time・Block・Msg・Packet・Processor・State）と、1 スロット分の指示
（Action・Instr）、状態遷移の原始関数、スロット単位の遷移 `State.step` と実行 `State.run`。
-/

namespace Minimmit

/-- view 番号。genesis のみ 0。 -/
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

/-- ブロック（§4）: genesis か、(view, 取引列, 親) の組。親はハッシュ値
    でなく親ブロックそのもの。取引列が相異なることは型に含まない。 -/
inductive Block (Tx : Type) : Type where
  | gen : Block Tx
  | node (v : View) (tr : List Tx) (parent : Block Tx) : Block Tx
deriving DecidableEq

/-- `b.view`。genesis は 0。 -/
def Block.view : Block Tx → View
  | .gen => ⟨0⟩
  | .node v _ _ => v

/-- `b.Tr`。genesis は空。 -/
def Block.tr : Block Tx → List Tx
  | .gen => []
  | .node _ tr _ => tr

/-- `b.par`。genesis には無い。 -/
def Block.parent : Block Tx → Option (Block Tx)
  | .gen => none
  | .node _ _ parent => some parent

/-- `b.Tr*`（§2）: b と全祖先の payload を古い順に連結した列。論文と違い重複を除去しない。 -/
def Block.trStar : Block Tx → List Tx
  | .gen => []
  | .node _ tr parent => parent.trStar ++ tr

/-- `Ancestor a b`: a は b の祖先（§2）。b 自身か、b の親の祖先。 -/
inductive Block.Ancestor : Block Tx → Block Tx → Prop where
  | refl (b : Block Tx) : Block.Ancestor b b
  | parent {a : Block Tx} (v : View) (tr : List Tx) (p : Block Tx) :
      Block.Ancestor a p → Block.Ancestor a (.node v tr p)

/-- メッセージ（§4）: 提案・票・nullify は署名者 q を持つ。ブロックの署名はブロックで
    なく message に付くので、票に埋め込まれた b は lead(v) の署名を運ばない。取引（§2）は
    環境の署名を持たず、Tx 型の値はすべて取引として扱う。 -/
inductive Msg (n : Nat) (Tx : Type) : Type where
  | block (q : Fin n) (b : Block Tx) : Msg n Tx
  | vote (q : Fin n) (b : Block Tx) : Msg n Tx
  | nullify (q : Fin n) (v : View) : Msg n Tx
  | tx (tr : Tx) : Msg n Tx
deriving DecidableEq

/-- 署名者。取引は環境の署名なので none。 -/
def Msg.signer {n : Nat} : Msg n Tx → Option (Fin n)
  | .block q _   => some q
  | .vote q _    => some q
  | .nullify q _ => some q
  | .tx _        => none

/-- プロセッサの局所状態（§4, Table 2）。 -/
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
  S : Finset (Msg n Tx)
  /-- 前スロット冒頭の S。`tick` で更新する。 -/
  prevS : Finset (Msg n Tx)

/-- 網に載る単位: どのメッセージが、誰宛に、いつ送られたか。 -/
structure Packet (n : Nat) (Tx : Type) where
  msg : Msg n Tx
  dst : Fin n
  sentAt : Time
deriving DecidableEq

/-- 大域状態: 全プロセッサの局所状態、腐敗集合、網に載った packet、現在のタイムスロット。 -/
structure State (n : Nat) (Tx : Type) where
  /-- 各プロセッサ。`procs i` が p_i。 -/
  procs : Fin n → Processor n Tx
  /-- これまでに腐敗したプロセッサ。 -/
  byz : Finset (Fin n)
  /-- 網に載った packet の全体。 -/
  pool : Finset (Packet n Tx)
  /-- 現在のタイムスロット。`State.tick` で進む。 -/
  now : Time

/-- p_i が自分から起こす動作: m を j へ送る、または次の view へ進む。 -/
inductive Action (n : Nat) (Tx : Type) : Type where
  | send (m : Msg n Tx) (j : Fin n) : Action n Tx
  | progress : Action n Tx

/-- 1 スロット分の指示。プロトコルの外から与えられるもの: 各プロセッサの動作の列、
    届く packet、環境が渡す取引、腐敗するプロセッサ。空のリストは「起きない」。 -/
structure Instr (n : Nat) (Tx : Type) where
  actions : Fin n → List (Action n Tx)
  deliveries : List (Packet n Tx)
  submits : List (Fin n × Tx)
  corrupts : List (Fin n)

namespace Processor

variable {n : Nat}

/-! ### 初期値 -/

/-- Table 2 の初期値: view 1、T = 0、フラグは false、notarised は ⊥、S は空。 -/
def init : Processor n Tx :=
  { view := ⟨1⟩, timer := 0, nullified := false, proposed := false, notarised := none,
    S := ∅, prevS := ∅ }

/-! ### 受信とスロット境界 -/

/-- 受信: S に m を入れる。到着と、自分の送信の即時受信（§4 冒頭）の両方が
    ここを通る。 -/
def receive [DecidableEq Tx] (p : Processor n Tx) (m : Msg n Tx) : Processor n Tx :=
  { p with S := insert m p.S }

/-- スロット境界: タイマー T を 1 進め、prevS をこのスロット冒頭の S（S₀）にする。 -/
def tick (p : Processor n Tx) (S₀ : Finset (Msg n Tx)) : Processor n Tx :=
  { p with timer := p.timer + 1, prevS := S₀ }

/-! ### 動作の局所効果
`Action` の 2 つに対応する。`State.execute` から呼ばれるほか、`Algo.step` が動作の列を
組み立てながら局所状態を追うのにも使う。 -/

/-- m を j へ送った局所状態への効果。m が自分の署名付きで現在の view のものなら、
    種類に応じてフラグを立てる。§4 の nullified・proposed・notarised は「現在の view で
    送ったか」の記録なので、他の view のもの、他人のもの、取引では何もしない。
    j が自分なら即時受信。 -/
def send [DecidableEq Tx] (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n) :
    Processor n Tx :=
  let p := match m with
    | .block q b   => if q = i ∧ b.view = p.view then { p with proposed := true } else p
    | .vote q b    => if q = i ∧ b.view = p.view then { p with notarised := some b } else p
    | .nullify q v => if q = i ∧ v = p.view then { p with nullified := true } else p
    | .tx _        => p
  if j = i then p.receive m else p

/-- 次の view へ（Algorithm 1 の 17 行と 21 行）: v := v + 1、T := 0、
    nullified・proposed := false、notarised := ⊥。S は触らない。 -/
def progress (p : Processor n Tx) : Processor n Tx :=
  { p with view := ⟨p.view.val + 1⟩, timer := 0,
           nullified := false, proposed := false, notarised := none }

end Processor

namespace State

variable {n : Nat}

/-! ### 補助 -/

/-- procs i だけを f で置き換える。 -/
def update (s : State n Tx) (i : Fin n) (f : Processor n Tx → Processor n Tx) :
    State n Tx :=
  { s with procs := Function.update s.procs i (f (s.procs i)) }

/-- packet x を網に載せる。`send` から呼ぶ。 -/
def transmit [DecidableEq Tx] (s : State n Tx) (x : Packet n Tx) : State n Tx :=
  { s with pool := insert x s.pool }

/-! ### 指示が起こす遷移
`Instr` の成分ごとに対応する。actions の各動作が send と progress、deliveries が deliver、
submits が submit、corrupts が corrupt。 -/

/-- p_i が m を j へ送る。m が自分の署名付きか受信済みのときだけ送り、そうでなければ
    何もしない（§2 の、署名は偽造できないという仮定）。局所状態への効果は
    `Processor.send`、網には now 付きの packet。 -/
def send [DecidableEq Tx] (s : State n Tx) (i : Fin n) (m : Msg n Tx) (j : Fin n) :
    State n Tx :=
  if m.signer = some i ∨ m ∈ (s.procs i).S then
    (s.update i (·.send i m j)).transmit ⟨m, j, s.now⟩
  else s

/-- p_i が次の view へ。 -/
def progress (s : State n Tx) (i : Fin n) : State n Tx :=
  s.update i Processor.progress

/-- packet x のメッセージが宛先に届く。x が pool にあるときだけ届き、そうでなければ
    何もしない。 -/
def deliver [DecidableEq Tx] (s : State n Tx) (x : Packet n Tx) : State n Tx :=
  if x ∈ s.pool then s.update x.dst (·.receive x.msg) else s

/-- 環境が p_j に取引 tr を渡す。 -/
def submit [DecidableEq Tx] (s : State n Tx) (j : Fin n) (tr : Tx) : State n Tx :=
  s.update j (·.receive (.tx tr))

/-- p_i が腐敗する。 -/
def corrupt (s : State n Tx) (i : Fin n) : State n Tx :=
  { s with byz := insert i s.byz }

/-! ### スロット単位の遷移
指示をスロット単位にまとめた遷移と、その繰り返し。 -/

/-- スロットを進める: 全プロセッサの `tick` と now + 1。s₀ はこのスロット冒頭の状態で、
    各プロセッサの prevS にその S を入れる。 -/
def tick (s₀ s : State n Tx) : State n Tx :=
  { s with procs := fun i => (s.procs i).tick (s₀.procs i).S, now := ⟨s.now.val + 1⟩ }

/-- p_i が動作 a を実行する。 -/
def execute [DecidableEq Tx] (s : State n Tx) (i : Fin n) : Action n Tx → State n Tx
  | .send m j => s.send i m j
  | .progress => s.progress i

/-- 1 スロット分の遷移。原始関数を 動作 → tick → deliver → submit → corrupt の順に
    固定している。tick と tick の間で原始関数がどの順に並んでも同じ状態に至ること、
    およびこの固定順で表せない挙動が「送ったスロットの中で届く配送」だけであることは、
    可換性による形式化の外の議論に依っていて未証明。 -/
def step [DecidableEq Tx] (s₀ : State n Tx) (instr : Instr n Tx) : State n Tx :=
  let s := (List.finRange n).foldl
    (fun s i => (instr.actions i).foldl (fun s a => s.execute i a) s) s₀
  let s := s.tick s₀
  let s := instr.deliveries.foldl deliver s
  let s := instr.submits.foldl (fun s x => s.submit x.1 x.2) s
  instr.corrupts.foldl corrupt s

/-- 実行: 初期状態 s₀ に指示の列 instrs を順に適用する。`instrs t` の deliveries と
    submits はスロット t + 1 に届く。`run s₀ instrs t` はスロット t の冒頭で、t に届いた
    message が S に入った状態。 -/
def run [DecidableEq Tx] (s₀ : State n Tx) (instrs : Nat → Instr n Tx) : Nat → State n Tx
  | 0 => s₀
  | t + 1 => (run s₀ instrs t).step (instrs t)

end State

/-! ### 指示の列についての語彙 -/

/-- p_i が m を送る（§5.1 の "sends"）: 指示の列のどこかに、誰か宛に m を送る動作がある。 -/
def Sends {n : Nat} (instrs : Nat → Instr n Tx) (i : Fin n) (m : Msg n Tx) : Prop :=
  ∃ t j, Action.send m j ∈ (instrs t).actions i

end Minimmit
