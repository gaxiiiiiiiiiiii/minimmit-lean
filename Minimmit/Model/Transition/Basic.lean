import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# 遷移系

1 スロット分の遷移 `State.step` と、その繰り返しである実行 `State.run` を定義する。
そのための §2・§4 の型（View・Time・Block・Msg・Packet）、プロセッサの局所状態
`Processor` と大域状態 `State` とそれぞれの原始関数、および 1 スロット分の指示 `Instr`。

## 論文からの差異

- ブロックは親をハッシュ値でなく親ブロックそのもので持つ。論文は暗号を完全と仮定していて
  ハッシュは衝突しないので、同一性についてはハッシュで参照することと直接持つことは
  区別できない。S がブロックを含むこと（§4 の規約）は `containsBlock` で別に言い、それは
  b を成分に持つ message の有無で決まって親には及ばない。祖先が S に入ることは
  Analysis/Liveness/Finalise で示す。
- 署名は、署名者を成分に持つことで表す。ブロックは `Block.node` の署名者、票と nullify は
  `Msg.vote`・`Msg.nullify` の署名者。提案 `Msg.propose` はブロックそのものを送り、提案の署名は
  持たない。論文の "lead(v) sends b" もブロック自体を送る。偽造不能は `State.send` のガード
  `Processor.canSend` で表す: 自分の署名付きか受信済みの message で、成分のブロックも自分の
  署名付きか S に含まれるものだけを送れる。
- `State.step` は 1 スロットの中の原始関数を 動作 → tick → 配送 → 取引 → 腐敗 の順に
  固定して適用する。tick と tick の間で原始関数がどの順に並んでも同じ状態に至ること、
  およびこの固定順で表せない挙動が「送ったスロットの中で届く配送」だけであることは、
  可換性による形式化の外の議論に依っていて未証明。
-/

namespace Minimmit

variable {n : Nat} {Tx : Type}

/-! ## 基本の型 -/

/-- view 番号、genesis のみ 0 -/
structure View where
  val : Nat
deriving DecidableEq

/-- タイムスロット -/
structure Time where
  val : Nat
deriving DecidableEq

/-- ブロック（§4）: genesis か、署名者と (view, 取引列, 親) の組。論文のブロックは lead(v) の
    署名付きの組で、その署名者を成分として持つ。親はハッシュ値でなく親ブロックそのもの。
    取引列が相異なることは型に含まない。 -/
inductive Block (n : Nat) (Tx : Type) : Type where
  | gen : Block n Tx
  | node (signer : Fin n) (v : View) (tr : List Tx) (parent : Block n Tx) : Block n Tx
deriving DecidableEq

/-- b の署名者、genesis なら none -/
def Block.signer : Block n Tx → Option (Fin n)
  | .gen => none
  | .node q _ _ _ => some q

/-- b の view、genesis なら 0 -/
def Block.view : Block n Tx → View
  | .gen => ⟨0⟩
  | .node _ v _ _ => v

/-- b の取引列 Tr、genesis なら空 -/
def Block.tr : Block n Tx → List Tx
  | .gen => []
  | .node _ _ tr _ => tr

/-- b の親、genesis には無い -/
def Block.parent : Block n Tx → Option (Block n Tx)
  | .gen => none
  | .node _ _ _ parent => some parent

/-- b の Tr*（§2）: b と全祖先の取引列を古い順に連結し、重複を先の出現だけ残して除いた列。
    親の Tr* にある取引を除いた自分の取引列を親の Tr* の後ろに付けるので、祖先の Tr* は
    接頭辞になる。 -/
def Block.trStar [DecidableEq Tx] : Block n Tx → List Tx
  | .gen => []
  | .node _ _ tr parent =>
    parent.trStar ++ (tr.filter fun x => decide (x ∉ parent.trStar)).eraseDups

/-- b の深さ: genesis からの距離。祖先の数より 1 少ない。 -/
def Block.depth : Block n Tx → Nat
  | .gen => 0
  | .node _ _ _ parent => parent.depth + 1

/-- `Ancestor a b`: a は b の祖先（§2）。b 自身か、b の親の祖先。 -/
inductive Block.Ancestor : Block n Tx → Block n Tx → Prop where
  | refl (b : Block n Tx) : Block.Ancestor b b
  | parent {a : Block n Tx} (q : Fin n) (v : View) (tr : List Tx) (p : Block n Tx) :
      Block.Ancestor a p → Block.Ancestor a (.node q v tr p)

/-- message（§4）: 提案はブロックそのもので、署名者はブロックの署名者。票と nullify は
    署名者 q を持つ。取引（§2）は環境が出すので署名者を持たず、Tx 型の値はすべて取引として
    扱う。 -/
inductive Msg (n : Nat) (Tx : Type) : Type where
  | propose (b : Block n Tx) : Msg n Tx
  | vote (q : Fin n) (b : Block n Tx) : Msg n Tx
  | nullify (q : Fin n) (v : View) : Msg n Tx
  | tx (tr : Tx) : Msg n Tx
deriving DecidableEq

/-- 署名者、プロセッサの署名を持たない取引では none -/
def Msg.signer : Msg n Tx → Option (Fin n)
  | .propose b   => b.signer
  | .vote q _    => some q
  | .nullify q _ => some q
  | .tx _        => none

/-- message が言及する view、取引では 0 -/
def Msg.view : Msg n Tx → View
  | .propose b   => b.view
  | .vote _ b    => b.view
  | .nullify _ v => v
  | .tx _        => ⟨0⟩

/-- message の成分にあるブロック、提案と票が持つ。 -/
def Msg.block : Msg n Tx → Option (Block n Tx)
  | .propose b => some b
  | .vote _ b  => some b
  | _          => none

/-- S がブロック b を含む（§4）: 成分に b を持つ message が S にある。 -/
def containsBlock [DecidableEq Tx] (S : Finset (Msg n Tx)) (b : Block n Tx) : Prop :=
  ∃ m ∈ S, m.block = some b

instance [DecidableEq Tx] (S : Finset (Msg n Tx)) (b : Block n Tx) :
    Decidable (containsBlock S b) :=
  inferInstanceAs (Decidable (∃ m ∈ S, _))

/-- Table 2 の初期の S: 全プロセッサの genesis への票。genesis と、その M-notarisation・
    L-notarisation に当たる。 -/
def genesisS (n : Nat) (Tx : Type) [DecidableEq Tx] : Finset (Msg n Tx) :=
  Finset.univ.image fun q => Msg.vote q .gen

theorem mem_genesisS [DecidableEq Tx] {m : Msg n Tx} :
    m ∈ genesisS n Tx ↔ ∃ q, m = .vote q .gen := by
  simp only [genesisS, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨q, h⟩ => ⟨q, h.symm⟩, fun ⟨q, h⟩ => ⟨q, h.symm⟩⟩

/-- ネットワークに載る単位: message、宛先、送信したスロット。 -/
structure Packet (n : Nat) (Tx : Type) where
  msg : Msg n Tx
  dst : Fin n
  sentAt : Time
deriving DecidableEq

/-! ## 局所状態
プロセッサの局所状態と、初期値・受信・送信・view 前進・スロット境界がそれに与える効果。
Table 2 の ⊥ は none で表す。
送信と view 前進は `State` の原始関数から呼ばれるほか、`Algo.step` が動作の列を
組み立てながら局所状態を追うのにも使う。 -/

/-- プロセッサの局所状態（§4, Table 2） -/
structure Processor (n : Nat) (Tx : Type) where
  /-- 現在の view、初期値 1 -/
  view : View
  /-- タイマー T、現在の view に入ってからのスロット数 -/
  timer : Nat
  /-- この view で nullify(v) を送ったか。 -/
  nullified : Bool
  /-- この view で提案したか。 -/
  proposed : Bool
  /-- この view で投票したブロック、未投票なら none -/
  notarised : Option (Block n Tx)
  /-- 受信した message の集合 -/
  S : Finset (Msg n Tx)
  /-- 前スロットの動作を終えた時点の S、`tick` で退避する -/
  prevS : Finset (Msg n Tx)

namespace Processor

/-- Table 2 の初期値: view 1、T = 0、フラグは false、notarised は none、S は genesis への
    全員の票。prevS も同じで、初期の S にあるものは転送の対象にならない。 -/
def init [DecidableEq Tx] : Processor n Tx :=
  { view := ⟨1⟩, timer := 0, nullified := false, proposed := false, notarised := none,
    S := genesisS n Tx, prevS := genesisS n Tx }

/-- 受信: S に m を入れる。到着と、自分の送信の即時受信（§4 冒頭）の両方が
    ここを通る。 -/
def receive [DecidableEq Tx] (p : Processor n Tx) (m : Msg n Tx) : Processor n Tx :=
  { p with S := insert m p.S }

/-- m を j へ送った局所状態への効果: m が自分の署名付きで現在の view のものなら、
    種類に応じてフラグを立てる。§4 の nullified・proposed・notarised は「現在の view で
    送ったか」の記録なので、他の view のもの、他人のもの、取引では何もしない。
    j が自分なら即時受信する。 -/
def send [DecidableEq Tx] (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) (j : Fin n) :
    Processor n Tx :=
  let p := match m with
    | .propose b   => if b.signer = some i ∧ b.view = p.view then { p with proposed := true } else p
    | .vote q b    => if q = i ∧ b.view = p.view then { p with notarised := some b } else p
    | .nullify q v => if q = i ∧ v = p.view then { p with nullified := true } else p
    | .tx _        => p
  if j = i then p.receive m else p

/-- 次の view へ（Algorithm 1 の 17 行と 21 行）: v := v + 1、T := 0、
    nullified・proposed := false、notarised := none。S は変えない。 -/
def progress (p : Processor n Tx) : Processor n Tx :=
  { p with view := ⟨p.view.val + 1⟩, timer := 0,
           nullified := false, proposed := false, notarised := none }

/-- スロット境界: タイマー T を 1 進め、S を prevS に退避する。 -/
def tick (p : Processor n Tx) : Processor n Tx :=
  { p with timer := p.timer + 1, prevS := p.S }

/-- m の成分のブロックが、自分の署名付きか S に含まれている。成分がなければ真。 -/
def blockOK [DecidableEq Tx] (S : Finset (Msg n Tx)) (i : Fin n) : Option (Block n Tx) → Prop
  | none => True
  | some b => b.signer = some i ∨ containsBlock S b

instance [DecidableEq Tx] (S : Finset (Msg n Tx)) (i : Fin n) (o : Option (Block n Tx)) :
    Decidable (blockOK S i o) := by
  cases o <;> simp only [blockOK] <;> infer_instance

/-- p_i が m を送れる（§2 の署名の偽造不能）: m が自分の署名付きか受信済みで、m の成分の
    ブロックも自分の署名付きか S に含まれている。 -/
def canSend [DecidableEq Tx] (p : Processor n Tx) (i : Fin n) (m : Msg n Tx) : Prop :=
  (m.signer = some i ∨ m ∈ p.S) ∧ blockOK p.S i m.block

instance [DecidableEq Tx] (p : Processor n Tx) (i : Fin n) (m : Msg n Tx) :
    Decidable (p.canSend i m) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Processor

/-! ## 大域状態
全プロセッサの局所状態とネットワークを合わせた大域状態と、1 つの送信・view 前進・配送・取引・腐敗・
スロット境界がそれに与える効果。 -/

/-- 大域状態: 全プロセッサの局所状態、腐敗集合、ネットワークに載った packet、現在のタイムスロット。 -/
structure State (n : Nat) (Tx : Type) where
  /-- 各プロセッサ、`procs i` が p_i -/
  procs : Fin n → Processor n Tx
  /-- これまでに腐敗したプロセッサ -/
  byz : Finset (Fin n)
  /-- ネットワークに載った packet の全体 -/
  pool : Finset (Packet n Tx)
  /-- 現在のタイムスロット、`State.tick` で進む -/
  now : Time

namespace State

/-- procs i だけを f で置き換える。 -/
def update (s : State n Tx) (i : Fin n) (f : Processor n Tx → Processor n Tx) :
    State n Tx :=
  { s with procs := Function.update s.procs i (f (s.procs i)) }

/-- packet x をネットワークに載せる。`send` から呼ぶ。 -/
def transmit [DecidableEq Tx] (s : State n Tx) (x : Packet n Tx) : State n Tx :=
  { s with pool := insert x s.pool }

/-- p_i が m を j へ送る。`Processor.canSend` を満たすときだけ送り、そうでなければ何もしない。
    §2 の、署名は偽造できないという仮定に当たる。局所状態には `Processor.send` の効果、
    ネットワークには now 付きの packet。 -/
def send [DecidableEq Tx] (s : State n Tx) (i : Fin n) (m : Msg n Tx) (j : Fin n) :
    State n Tx :=
  if (s.procs i).canSend i m then
    (s.update i (·.send i m j)).transmit ⟨m, j, s.now⟩
  else s

/-- p_i が次の view へ進む。 -/
def progress (s : State n Tx) (i : Fin n) : State n Tx :=
  s.update i Processor.progress

/-- packet x の message が宛先に届く。x が pool にあるときだけ届き、そうでなければ
    何もしない。 -/
def deliver [DecidableEq Tx] (s : State n Tx) (x : Packet n Tx) : State n Tx :=
  if x ∈ s.pool then s.update x.dst (·.receive x.msg) else s

/-- 環境が p_j に取引 tr を渡す。 -/
def submit [DecidableEq Tx] (s : State n Tx) (j : Fin n) (tr : Tx) : State n Tx :=
  s.update j (·.receive (.tx tr))

/-- p_i が腐敗する。 -/
def corrupt (s : State n Tx) (i : Fin n) : State n Tx :=
  { s with byz := insert i s.byz }

/-- スロットを進める: 全プロセッサの `tick` と now + 1。 -/
def tick (s : State n Tx) : State n Tx :=
  { s with procs := fun i => (s.procs i).tick, now := ⟨s.now.val + 1⟩ }

end State

/-! ## 指示
1 スロット分にプロトコルの外から与えられるもの。`Instr` の成分は `State.step` の段階に
対応する: actions の各動作が `execute`、deliveries が `deliver`、submits が `submit`、
corrupts が `corrupt`。 -/

/-- p_i が自分から起こす動作: m を j へ送る、または次の view へ進む。 -/
inductive Action (n : Nat) (Tx : Type) : Type where
  | send (m : Msg n Tx) (j : Fin n) : Action n Tx
  | progress : Action n Tx

/-- プロトコルの外から与えられる 1 スロット分の指示: 各プロセッサの動作の列、届く packet、
    環境が渡す取引、腐敗するプロセッサ。空のリストは、その種類のことが起きないことを表す。 -/
structure Instr (n : Nat) (Tx : Type) where
  actions : Fin n → List (Action n Tx)
  deliveries : List (Packet n Tx)
  submits : List (Fin n × Tx)
  corrupts : List (Fin n)

/-- p_i が m を送る（§5.1 の "sends"）: 指示の列のどこかに、誰か宛に m を送る動作がある。
    ガードを通らない動作も含み、ネットワークに載ったかどうかは `State.send` の効果で決まる。 -/
def Sends (instrs : Nat → Instr n Tx) (i : Fin n) (m : Msg n Tx) : Prop :=
  ∃ t j, Action.send m j ∈ (instrs t).actions i

/-! ## スロット遷移と実行 -/

namespace State

/-- p_i が動作 a を実行する。 -/
def execute [DecidableEq Tx] (s : State n Tx) (i : Fin n) : Action n Tx → State n Tx
  | .send m j => s.send i m j
  | .progress => s.progress i

/-- 1 スロット分の遷移: 原始関数を 動作 → tick → deliver → submit → corrupt の順に
    適用する。動作で送った packet の刻印 sentAt は tick 前の now なので、`instrs t` の動作で
    送った packet は t を持つ。 -/
def step [DecidableEq Tx] (s : State n Tx) (instr : Instr n Tx) : State n Tx :=
  let s := (List.finRange n).foldl
    (fun s i => (instr.actions i).foldl (fun s a => s.execute i a) s) s
  let s := s.tick
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

end Minimmit
