# 論文との対応

論文 Minimmit（Chou, Lewis-Pye, O'Grady, [arXiv:2508.10862](https://arxiv.org/abs/2508.10862)）の記述が本形式化のどの定義と定理に当たるか、そこで本形式化が決めたこと、論文と違う形にした点。各項目は、論文の原文、それに当たる Lean の宣言、その宣言に付属する宣言の 3 つの枠からなる。論文の文は原文のまま引き、疑似コードと表はそのままの形で引く。論文に定義の文がない項目は原文の枠を置かず、何に当たるかを一文で述べ、論文が触れている文があれば補足で成分の隣に引く。Lean の宣言は、原文に当たるものと主定理を docstring とコメントを省いて引く。付属する宣言はコードを引かず、属性は名前だけを、付属は名前と語句を並べる。Algorithm 1 の節では疑似コードの部分ごとに項目を立て、実装の前に、そこで使う条件と処理の定義を「発動条件」「処理内容」の枠で引く。宣言に現れる n・Tx と、定理文の f・Δ・δ・GST・lead・s₀・instrs は、各ファイルの冒頭で `variable` として宣言した暗黙の引数。定義と定理の所在は README の「ファイル構成」にある。

## 1. 対象

基準は論文の v7（2026-01-27）。対象は §4 の Algorithm 1 と §5 の Lemma 5.1〜5.10 で、§2 のモデルはそのために必要な範囲で形式化した。§2 の Consistency と Liveness は論文の定義どおりの文で定義し、Lemma 5.4 と 5.7 として証明した。§6 の最適化は対象外。

論文の証明に誤りは見つからなかった。ただし論文の主張が成り立つのは、Algorithm 1 の実行方式を調整し、いくつかを論文と違う形にしたうえでのことである。

定理と論文の補題の対応は README の「状態」の表にある。`sorry` はなく、各主定理の依存公理は `propext`・`Classical.choice`・`Quot.sound` だけで、主定理を並べた Axioms.lean がこれを `#guard_msgs` で固定し、CI がビルドと公理の監査を回す。定理の仮定が同時に満たせることは `constraints_satisfiable` が示し、定理は空虚に真ではない。

## 2. プロトコル

### 2.1 表現

#### ■ 基本の型

view 番号とタイムスロットの型。どちらも自然数を包む構造体。

- **実装**

  ```lean
  structure View where
    val : Nat
  deriving DecidableEq
  ```

  ```lean
  structure Time where
    val : Nat
  deriving DecidableEq
  ```

  - `View` の 0 は genesis を意味する。

#### ■ ブロック

- **原文**

  > The genesis block is the tuple b_gen := (0, λ, λ), where λ denotes the empty sequence (of length 0). A block other than the genesis block is a tuple b = (v, Tr, h), signed by lead(v), where: v ∈ N≥1 (thought of as the view corresponding to b); Tr is a sequence of distinct transactions; h is a hash value (used to specify b's parent). We also write b.view, b.Tr and b.par to denote the corresponding entries of b.

- **実装**

  ```lean
  inductive Block (n : Nat) (Tx : Type) : Type where
    | gen : Block n Tx
    | node (signer : Fin n) (v : View) (tr : List Tx) (parent : Block n Tx) : Block n Tx
  deriving DecidableEq
  ```

  - `Tx` は取引の型で、ブロックはこれを引数にとる。取引の中身には立ち入らない。
  - `signer` は署名者で、原文の「signed by lead(v)」の lead(v) に当たる。
  - `tr` は Tr。相異なる列であることは型に含めない。Tr* が重複を除くので定理は影響を受けず、重複を含む組を許す分だけ広い範囲で成り立つ。
  - `parent` は親ブロックそのもの。原文はハッシュ値 h で参照している。

- **属性**

  - `Block.signer`
  - `Block.view`
  - `Block.tr`
  - `Block.parent`
  - `Block.depth`

#### ■ 祖先

- **原文**

  > The ancestors of b are b and all ancestors of its parent (while the genesis block has only itself as ancestor), and each block has the genesis block as an ancestor.

- **実装**

  ```lean
  inductive Block.Ancestor : Block n Tx → Block n Tx → Prop where
    | refl (b : Block n Tx) : Block.Ancestor b b
    | parent {a : Block n Tx} (q : Fin n) (v : View) (tr : List Tx) (p : Block n Tx) :
        Block.Ancestor a p → Block.Ancestor a (.node q v tr p)
  ```

#### ■ message

- **原文**

  > In what follows, we suppose that all messages are signed by the sender.

  > block b ≠ b_gen: A tuple (v, Tr, h), signed by lead(v)  
  > vote for b: A message (vote, b)  
  > nullify(v): A message of the form (nullify, v)

  > Transactions are messages of a distinguished form, signed by the environment. … We make the standard assumption that transactions are unique

- **実装**

  ```lean
  inductive Msg (n : Nat) (Tx : Type) : Type where
    | propose (b : Block n Tx) : Msg n Tx
    | vote (q : Fin n) (b : Block n Tx) : Msg n Tx
    | nullify (q : Fin n) (v : View) : Msg n Tx
    | tx (tr : Tx) : Msg n Tx
  deriving DecidableEq
  ```

  - 対応は、block が `propose b`、vote for b が `vote q b`、nullify(v) が `nullify q v`、transaction が `tx tr`。`vote q b` と `nullify q v` の q が署名者。
  - 署名は署名者の成分で表す。
  - 取引の message にも環境からの署名が要るが、署名者が環境と決まっていて特定する必要がないので、`tx tr` には署名者の成分を置かない。
  - 原文では、内容が同じで別の取引は無いと仮定している。本形式化では内容が同じ取引は区別がつかないので、仮定は成り立つ。

- **属性**

  - `Msg.signer`
  - `Msg.view`
  - `Msg.block`

#### ■ 局所状態

- **原文**

  > v: Initially 1, specifies the present view  
  > T: Initially 0, a local timer reset upon entering each view  
  > nullified: Initially false, specifies whether already sent nullify(v) message  
  > proposed: Initially false, specifies whether already proposed a block for view v  
  > notarised: Initially set to ⊥, records block voted for in present view  
  > S: Records all received messages, automatically updated. Initially contains only b_gen and M/L-notarisations for b_gen
  >
  > We also regard S as containing a block b whenever S contains any message (tuple) with b as one of its entries.

- **実装**

  ```lean
  structure Processor (n : Nat) (Tx : Type) where
    view : View
    timer : Nat
    nullified : Bool
    proposed : Bool
    notarised : Option (Block n Tx)
    S : Finset (Msg n Tx)
    prevS : Finset (Msg n Tx)
  ```

  - ⊥ は none。
  - `prevS` は論文にない補助で、前スロットの動作を終えた時点の S。「新しい」証明書の判定に `forwardNew` が使う。

- **付属**

  - `Processor.init` : 初期値
  - `genesisS` : 初期の S。b_gen と M/L-notarisation は message の集合では持てないので、全員の genesis への票で表す
  - `containsBlock` : S がブロックを含むこと。ブロックは再帰的に先祖の情報も持つが、判定は message が直接持つブロックだけを対象とする
  - `Processor.receive` : S に m を入れる、pool からの受信と自分の送信の即時受信がここを通る
  - `Processor.send` : p_i が m を j へ送ったときの効果、現在の view の自分の m なら種類に応じて proposed・notarised・nullified を更新し、j = i なら即時受信
  - `Processor.progress` : 17 行と 21 行の view の前進
  - `Processor.tick` : スロット境界、T を 1 進めて S を prevS に退避

### 2.2 証明書

論文の証明書は票や nullify の集合だが、本形式化は証明書を物として持たず、S がそれを含むことを S 上の述語で言う。証明書は、b への票の署名者の集合 `voters` と、nullify(v) の署名者の集合 `nullifiers` の要素数で数える。署名者で集めるので、原文の「each signed by a different processor」は要素数に含まれる。

#### ■ M-notarisation

- **原文**

  > An M-notarisation for the block b is a set of 2f + 1 votes for b, each signed by a different processor.

- **実装**

  ```lean
  def MNotarised (f : Nat) (S : Finset (Msg n Tx)) (b : Block n Tx) : Prop :=
    2 * f + 1 ≤ (voters S b).card
  ```

#### ■ L-notarisation

- **原文**

  > An L-notarisation for the block b is a set of n − f votes for b, each signed by a different processor.

- **実装**

  ```lean
  def LNotarised (f : Nat) (S : Finset (Msg n Tx)) (b : Block n Tx) : Prop :=
    n - f ≤ (voters S b).card
  ```

#### ■ nullification

- **原文**

  > A nullification for view v is a set of 2f + 1 nullify(v) messages, each signed by a different processor.

- **実装**

  ```lean
  def Nullified (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Prop :=
    2 * f + 1 ≤ (nullifiers S v).card
  ```

### 2.3 実行モデル

論文は §2 で、Byzantine な敵対者のもとでの部分同期のシステムモデルを言葉で述べ、定義の形では与えていない。本形式化はこれを状態遷移系として定める。状態が `State`、1 スロット分の遷移が `State.step` で、敵対者の自由度は指示 `Instr` に切り出して遷移の入力にする。実行 `State.run` は、指示の列を初期状態から順に適用して得る状態の列。

#### ■ 大域状態

本形式化の `State` は、ある時点で実行が到達している状況の全体に当たる。

- **実装**

  ```lean
  structure State (n : Nat) (Tx : Type) where
    procs : Fin n → Processor n Tx
    byz : Finset (Fin n)
    pool : Finset (Packet n Tx)
    now : Time
  ```

  ```lean
  structure Packet (n : Nat) (Tx : Type) where
    msg : Msg n Tx
    dst : Fin n
    sentAt : Time
  deriving DecidableEq
  ```

  - `procs` は n 個のプロセッサそれぞれの局所状態を並べる。原文は「We consider a set Π = {p_1, . . . , p_n} of n processors.」と番号を 1 から振るが、本形式化は `Fin n` で 0 から数える。
  - `byz` はこれまでに腐敗したプロセッサを集める。原文の「at most f processors may become corrupted by the adversary during the course of the execution」に当たり、腐敗は取り消せないので `byz` は増える一方になる。一度も `byz` に入らないプロセッサが、原文が correct と呼ぶプロセッサに当たる。
  - `pool` は送られた packet の全体を持つ。原文の「Processors communicate by point-to-point authenticated channels.」の通信路に当たり、`Packet` は message に宛先 `dst` を添えて 1 対 1 の送信を表す。届いた packet も取り除かず `pool` に残す。
  - `sentAt` は packet を送ったスロットを覚える。原文の「a message sent at time t must arrive at time t′ > t with t′ ≤ max{GST, t} + Δ」の t に当たり、受信の期限を測るのに使う。
  - `now` は現在のスロットを指す。原文の「the execution is divided into discrete timeslots t ∈ N≥0」の t に当たる。

- **付属**

  - `State.update` : procs i を f で置き換える
  - `State.transmit` : pool に packet を加える
  - `State.send` : 送信のガードを通るときだけ、`Processor.send` の効果と now を刻印した packet の追加
  - `State.progress` : p_i に `Processor.progress` を適用
  - `State.deliver` : pool にある packet だけを宛先の S に入れる
  - `State.submit` : p_j の S に取引を入れる
  - `State.corrupt` : byz に i を加える
  - `State.tick` : 全プロセッサの `Processor.tick` と now + 1
  - `State.execute` : 動作の実行、`State.send` か `State.progress`

#### ■ 動作

プロセッサの動作は、message を誰かへ送ることと、次の view へ進むことの 2 つからなる。

- **実装**

  ```lean
  inductive Action (n : Nat) (Tx : Type) : Type where
    | send (m : Msg n Tx) (j : Fin n) : Action n Tx
    | progress : Action n Tx
  ```

#### ■ 指示

プロトコルは 1 スロットの進み方を一通りには決めない。指示は、決まらずに残る選択をスロットごとに 1 つにまとめたものに当たる。

- **実装**

  ```lean
  structure Instr (n : Nat) (Tx : Type) where
    actions : Fin n → List (Action n Tx)
    deliveries : List (Packet n Tx)
    submits : List (Fin n × Tx)
    corrupts : List (Fin n)
  ```

  - `actions` は、各プロセッサがそのスロットで行う動作の列を、プロセッサごとに与える。
  - `deliveries` はこのスロットに届く packet。原文の「The adversary chooses GST and also message delivery times, subject to the constraints already defined.」の受信時刻の選択に当たる。
  - `submits` は環境が渡す取引とその宛先。原文の「Each timeslot, each processor may receive some finite set of transactions directly from the environment.」に当たる。
  - `corrupts` はこのスロットで腐敗するプロセッサ。原文の「at most f processors may become corrupted by the adversary during the course of the execution」の腐敗させる選択に当たる。

#### ■ スロット遷移

1 スロット分の指示を大域状態に適用して、次のスロットの冒頭の状態を返す。

- **実装**

  ```lean
  def step [DecidableEq Tx] (s : State n Tx) (instr : Instr n Tx) : State n Tx :=
    let s := (List.finRange n).foldl
      (fun s i => (instr.actions i).foldl (fun s a => s.execute i a) s) s
    let s := s.tick
    let s := instr.deliveries.foldl deliver s
    let s := instr.submits.foldl (fun s x => s.submit x.1 x.2) s
    instr.corrupts.foldl corrupt s
  ```

  - プロセッサの動作、時刻の前進、packet の受信、新しい取引の投入、腐敗の順に適用する。論文ではスロット内の事象の順序を定めていない。本形式化ではこの順に固定する。この固定が挙動を狭めないことは未証明。
  - この順序により、`instrs t` の動作で送る packet の sentAt は t になり、その message が宛先の S に入るのは早くてもスロット t + 1 の冒頭になる。原文の「a message sent at time t must arrive at time t′ > t」はこれで満たされる。

#### ■ 実行

論文の execution に当たる。初期状態と指示の列から、各スロットまでを実行した状態を定める。

- **実装**

  ```lean
  def run [DecidableEq Tx] (s₀ : State n Tx) (instrs : Nat → Instr n Tx) : Nat → State n Tx
    | 0 => s₀
    | t + 1 => (run s₀ instrs t).step (instrs t)
  ```

### 2.4 暗号の仮定

論文は署名方式と公開鍵基盤と衝突困難なハッシュ関数を使い、敵対者がそれらを破れない実行だけを考える。本形式化は暗号を持たず、3 つの対応で同じ仮定を表す。署名は、ブロックと message に署名者の成分を持たせることで表す。署名を偽造できないことは、送信のガードで表す。ハッシュによる親の参照は、親ブロックを値として持つことで表し、衝突困難の仮定は要らなくなる。

#### ■ 署名の偽造不能

- **原文**

  > We use a cryptographic signature scheme, a public key infrastructure (PKI) to validate signatures, and a collision resistant hash function H. … we restrict attention to executions in which the adversary is unable to break these cryptographic schemes.

- **実装**

  ```lean
  def canSend [DecidableEq Tx] (p : Processor n Tx) (i : Fin n) (m : Msg n Tx) : Prop :=
    (m.signer = some i ∨ m ∈ p.S) ∧ blockOK p.S i m.block
  ```

  - p_i が送れるのは、自分の署名付きか受信済みの message で、成分のブロックも自分の署名付きか S に含まれるもの。他人の署名付きの message とブロックを作れないことが偽造不能に当たり、受信済みのものは転送できる。`State.send` はガードを通らない送信を無視する。
  - ガードは腐敗者にもかかる。

- **付属**

  - `blockOK` : 成分のブロックが自分の署名付きか S に含まれること、成分がなければ真

### 2.5 Algorithm 1

論文の Algorithm 1 は、各スロットに各プロセッサが行う処理の疑似コードである。本形式化では `step` がこれに当たり、疑似コードの各部分を関数にして順に適用する。疑似コードは上から 1 回だけ実行する書き方だが、証明は、条件が成り立てばその都度処理されることを前提にしている。1 回実行するだけではこの前提を満たさないので、本形式化は評価の順序を変え、view の前進を証明書がある限り繰り返す。

#### ■ 補助関数

疑似コードの各部分の実装が共通して使う関数。

- `disseminate (i : Fin n) (p : Processor n Tx) (m : Msg n Tx) : Processor n Tx × List (Action n Tx)`  
  m を全員へ送る動作の列とその後の局所状態、疑似コードの disseminate
- `disseminateAll (i : Fin n) (p : Processor n Tx) (ms : List (Msg n Tx)) : Processor n Tx × List (Action n Tx)`  
  ms を順に全員へ送る
- `votedBlocks (S : Finset (Msg n Tx)) : List (Block n Tx)`  
  S にある票のブロックの列
- `nullifyViews (S : Finset (Msg n Tx)) : List View`  
  S にある nullify の view の列
- `proposals (lead : View → Fin n) (S : Finset (Msg n Tx)) (v : View) : List (Block n Tx)`  
  S が含む lead(v) の署名付きの view v のブロックの列、valid proposal の候補
- `mNotarisedAt (f : Nat) (S : Finset (Msg n Tx)) (v : View) : List (Block n Tx)`  
  S にある M-notarisation を持つ view v のブロックの列
- `maxView (S : Finset (Msg n Tx)) : Nat`  
  S にある message が言及する view の最大
- `leastNullifiers (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Finset (Fin n)`  
  nullify(v) の署名者のうち番号順の先頭 2f + 1 人、原文の「lexicographically least」
- `leastVoters (f : Nat) (S : Finset (Msg n Tx)) (b : Block n Tx) : Finset (Fin n)`  
  b への票の署名者のうち番号順の先頭 2f + 1 人

#### ■ view の前進

- **原文**

  > ```
  > 16:   If S contains a nullification for v:
  > 17:      Set v := v + 1, nullified := false, proposed := false, notarised := ⊥, T := 0;
  > 18:                                                                         ⊲ Go to next view
  > 19:   If S contains an M-notarisation for some b with b.view = v:
  > 20:      If notarised = ⊥ and nullified = false, disseminate (vote, b);             ⊲ Send vote
  > 21:      Set v := v + 1, nullified := false, proposed := false, notarised := ⊥, T := 0;
  > 22:                                                                         ⊲ Go to next view
  > ```

- **発動条件**

  S に現在の view の証明書がある。

  ```lean
  def HasCert (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Prop :=
    Nullified f S v ∨ mNotarisedAt f S v ≠ []
  ```

  - `HasCert` は、16 行と 19 行の条件の選言に当たる。

- **処理内容**

  `advanceOnce` は 1 回分の前進で、nullification があれば進み、なければ M-notarisation のあるブロックに未投票なら票を入れてから進む。

  ```lean
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
  ```

  - 19 行の「some b」は `mNotarisedAt` の先頭とする。論文の証明は b の選び方によらない。

- **実装**

  `climb` は、現在の view の証明書がある限り、`advanceOnce` を繰り返す。

  ```lean
  noncomputable def climb (f : Nat) (i : Fin n) :
      Nat → Processor n Tx → Processor n Tx × List (Action n Tx)
    | 0, p => (p, [])
    | fuel + 1, p =>
      if HasCert f p.S p.view then
        let r := advanceOnce f i p
        let r' := climb f i fuel r.1
        (r'.1, r.2 ++ r'.2)
      else (p, [])
  ```

  - 原文は 16〜21 行を 1 スロットに 1 回評価するが、`climb` は証明書がある限り繰り返す。
  - `climb` の fuel は論文にない引数で、Lean の停止性のために繰り返しの上限を与える。`step` は `maxView` + 1 を渡す。この上限で打ち切られないこと、すなわち `climb` の後に現在の view の証明書が残らないことは `st1_quiescent` が示す。

- **付属**

  - `advanceM` : `advanceOnce` の 19〜21 行の側、証明で使う

#### ■ 提案

- **原文**

  > ```
  >  5:   If p_i = lead(v) and proposed = false:
  >  6:      ProposeChild(SelectParent(S, v), v);                             ⊲ Send out a new block
  >  7:      Set proposed := true;
  > ```
  >
  > The function SelectParent(S, v). This function is used by the leader of a view, p_i say, to select the parent block to build on. If v′ < v is the greatest view such that S contains an M-notarisation for some b with b.view = v′, and if b is the lexicographically least such block, the function outputs b.
  >
  > There must exist such a view, since S always contains an M-notarisation for the genesis block.
  >
  > The procedure ProposeChild(b, v). This procedure is executed by the leader p_i of view v to determine a new block. To execute the procedure, p_i: Forms a sequence of distinct transactions Tr, containing all transactions received by p_i and not included in b′.Tr for any b′ ∈ S which is an ancestor of b, and; Disseminates the block (v, Tr, H(b)).

- **発動条件**

  自分が lead(v) で未提案。

  ```lean
  lead p.view = i ∧ p.proposed = false
  ```

- **処理内容**

  SelectParent で親を選び、ProposeChild で子のブロックを作って全員へ送る。SelectParent が `selectParent`、ProposeChild の Tr の作成が `payload` に当たる。

  ```lean
  noncomputable def selectParent (f : Nat) (S : Finset (Msg n Tx)) (v : View) : Block n Tx :=
    (((votedBlocks S).filter fun b => decide (b.view.val < v.val ∧ MNotarised f S b)).argmax
      fun b => b.view.val).getD .gen
  ```

  ```lean
  noncomputable def payload (S : Finset (Msg n Tx)) (b : Block n Tx) : List Tx :=
    (S.toList.filterMap fun m => match m with | .tx tr => some tr | _ => none).filter
      fun tr => decide (∀ a, Block.Ancestor a b → containsBlock S a → tr ∉ a.tr)
  ```

  - 原文の「lexicographically least」は、本形式化では S の列挙順で最初に現れるものになる。論文の証明はこの選び方によらない。
  - 候補が無いときの genesis は既定値で、原文の脚注のとおり候補は常にあるので使われない。

  子のブロックを組み立てて全員へ送る式。

  ```lean
  let parent := selectParent f p.S p.view
  disseminate i p (.propose (.node i p.view (payload p.S parent) parent))
  ```

- **実装**

  ```lean
  noncomputable def propose (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
      Processor n Tx × List (Action n Tx) :=
    if lead p.view = i ∧ p.proposed = false then
      let parent := selectParent f p.S p.view
      disseminate i p (.propose (.node i p.view (payload p.S parent) parent))
    else (p, [])
  ```

#### ■ 投票

- **原文**

  > ```
  >  9:   If S contains a valid proposal b for view v:                      ⊲ As defined in Section 4
  > 10:      If notarised = ⊥ and nullified = false:
  > 11:         Set notarised := b and disseminate (vote, b);                            ⊲ Send vote
  > ```
  >
  > When S contains a valid proposal for view v. This condition is satisfied when S contains: (i) Precisely one block b of the form b = (v, Tr, h) signed by lead(v); (ii) An M-notarisation for some b′ with H(b′) = h, and with b′.view = v′ (say), and; (iii) A nullification for each view in the open interval (v′, v). When (i)–(iii) are satisfied w.r.t. b, we say S contains a valid proposal b for view v.

- **発動条件**

  S に view v の valid proposal b があり、未投票かつ未 nullify。

  ```lean
  structure ValidProposal (f : Nat) (lead : View → Fin n) (S : Finset (Msg n Tx)) (v : View)
      (b : Block n Tx) : Prop where
    view : b.view = v
    signed : b.signer = some (lead v)
    mem : containsBlock S b
    unique : ∀ b', b'.view = v → b'.signer = some (lead v) → containsBlock S b' → b' = b
    ne_gen : b ≠ .gen
    parent : ∀ p ∈ b.parent, MNotarised f S p
    gaps : ∀ p ∈ b.parent, ∀ w : View, p.view.val < w.val → w.val < v.val → Nullified f S w
  ```

  - (i) が `view`・`signed`・`mem`・`unique`、(ii) が `parent`、(iii) が `gaps` に当たる。
  - `ne_gen` は、b が組 (v, Tr, h) の形であること、すなわち genesis でないことに当たる。
  - (ii) の H(b′) = h は、本形式化ではブロックが親を値で持つので、b′ が b の親そのものであることに当たる。
  - 10 行の notarised = ⊥ と nullified = false は、実装が直接判定する。

- **処理内容**

  自分の票を全員へ送る。

  ```lean
  disseminate i p (.vote i b)
  ```

- **実装**

  ```lean
  noncomputable def voteProposal (f : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
      Processor n Tx × List (Action n Tx) :=
    match proposals lead p.S p.view with
    | [b] =>
      if ValidProposal f lead p.S p.view b ∧ p.notarised = none ∧ p.nullified = false then
        disseminate i p (.vote i b)
      else (p, [])
    | _ => (p, [])
  ```

  - 9 行の b は、`proposals` がちょうど 1 つ返すときのそれ。

#### ■ timeout

- **原文**

  > ```
  > 13:   If T = 2Δ, nullified = false and notarised = ⊥:
  > 14:      Set nullified := true and disseminate (nullify, v);                   ⊲ Send nullify(v)
  > ```

- **発動条件**

  T = 2Δ で未 nullify かつ未投票。T は `timer` で、`Processor.tick` が 1 ずつ進める。

  ```lean
  p.timer = 2 * Δ ∧ p.nullified = false ∧ p.notarised = none
  ```

- **処理内容**

  nullify(v) を全員へ送る。

  ```lean
  disseminate i p (.nullify i p.view)
  ```

- **実装**

  ```lean
  def nullifyTimeout (Δ : Nat) (i : Fin n) (p : Processor n Tx) :
      Processor n Tx × List (Action n Tx) :=
    if p.timer = 2 * Δ ∧ p.nullified = false ∧ p.notarised = none then
      disseminate i p (.nullify i p.view)
    else (p, [])
  ```

#### ■ proof of no progress

- **原文**

  > ```
  > 24:   If nullified = false, notarised ≠ ⊥ and S contains ≥ 2f + 1 messages, each signed by a
  > 25:   different processor, and each either:
  > 26:    (i) A message (nullify, v), or;
  > 27:    (ii) Of the form (vote, b) for some b s.t. b.view = v and notarised ≠ b:
  > 28:       Set nullified := true and disseminate (nullify, v);
  > 29:                                  ⊲ Send nullify(v) message upon proof of no progress for v
  > ```

- **発動条件**

  未 nullify で投票済みのとき、S に、nullify(v) か自分の投票先と違う view v のブロックへの票が 2f + 1 人分ある。

  ```lean
  inductive NoProgressWitness (S : Finset (Msg n Tx)) (v : View) (notarised : Option (Block n Tx))
      (q : Fin n) : Prop where
    | nullify (h : Msg.nullify q v ∈ S) : NoProgressWitness S v notarised q
    | vote (b : Block n Tx) (hv : b.view = v) (hne : some b ≠ notarised)
        (h : Msg.vote q b ∈ S) : NoProgressWitness S v notarised q
  ```

  ```lean
  noncomputable def noProgressWitnesses (S : Finset (Msg n Tx)) (v : View)
      (notarised : Option (Block n Tx)) : Finset (Fin n) :=
    Finset.univ.filter (NoProgressWitness S v notarised)
  ```

  ```lean
  def NoProgress (f : Nat) (S : Finset (Msg n Tx)) (v : View)
      (notarised : Option (Block n Tx)) : Prop :=
    2 * f + 1 ≤ (noProgressWitnesses S v notarised).card
  ```

  - `NoProgressWitness` は、プロセッサ q が (i) か (ii) の message を S に持つことを表す。
  - `NoProgress` は、そのような q が 2f + 1 人以上いることを表す。24〜27 行の分岐条件のうち S についての部分に当たり、nullified = false と notarised ≠ ⊥ は実装が直接判定する。

- **処理内容**

  nullify(v) を全員へ送る。

  ```lean
  disseminate i p (.nullify i p.view)
  ```

- **実装**

  ```lean
  noncomputable def nullifyNoProgress (f : Nat) (i : Fin n) (p : Processor n Tx) :
      Processor n Tx × List (Action n Tx) :=
    if p.nullified = false ∧ p.notarised ≠ none ∧ NoProgress f p.S p.view p.notarised then
      disseminate i p (.nullify i p.view)
    else (p, [])
  ```

#### ■ 新しい証明書の転送

- **原文**

  > ```
  >  2:   Disseminate new nullifications in S;                        ⊲ ‘new’ as defined in Section 4
  >  3:   Disseminate new M-notarisations in S;
  > ```
  >
  > Processors will be required to forward on all newly received nullifications and M-notarisations. … At timeslot t, p_i regards a nullification N ⊆ S for some view v (not necessarily equal to v) as new if: S (as locally defined) did not contain a nullification for view v at any smaller timeslot, and; N is lexicographically least amongst nullifications for view v contained in S. At timeslot t, p_i regards an M-notarisation Q ⊆ S for block b as new if: S did not contain an M-notarisation for b at any smaller timeslot, and; Q is lexicographically least amongst M-notarisations for b contained in S.
  >
  > Since it is not necessary for liveness, our pseudocode does not require processors to forward L-notarisations.
  >
  > we also initially assume (without explicit mention in the pseudocode) that correct processors automatically send new transactions to all others upon first receiving them

- **発動条件**

  原文の new、すなわち S にあって prevS にないこと。実装が送るものを選ぶときに直接判定する。

  ```lean
  Nullified f p.S v ∧ ¬ Nullified f p.prevS v
  ```

  ```lean
  MNotarised f p.S b ∧ ¬ MNotarised f p.prevS b
  ```

- **処理内容**

  送る message の列を作り、`disseminateAll` で全員へ送る。`forwardMsgs` は実装と同じ計算で列だけを返す。

  ```lean
  noncomputable def forwardMsgs (f : Nat) (p : Processor n Tx) : List (Msg n Tx)
  ```

- **実装**

  ```lean
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
  ```

  - 「S did not contain … at any smaller timeslot」は、S にあって prevS にないこと。prevS は前スロットの動作を終えた時点の S なので、このスロットに届いたものと、自分の送信で完成した証明書をこのスロットで送る。最後尾で評価するので、その証明書での view の前進は次のスロット。
  - 初期の S にある genesis の証明書は、原文の定義では最初のスロットに new になるが、prevS の初期値を S と同じにしているので送らない。
  - 取引の転送は、S にあって prevS にない取引を送る。
  - L-notarisation は送らない。

#### ■ 確定

- **原文**

  > There is a unique genesis block b_gen, which is considered finalised at the start of the protocol execution. … When a processor p_i finalises b at timeslot t, this means that, upon obtaining all ancestors of b, it sets log_i(t) to extend b.Tr*.

  > ```
  > 31:   If S contains a new L-notarisation for any block b:
  > 32:      Finalise b;                                  ⊲ Finalisation as specified in Section 2
  > ```

- **発動条件**

  S に b の L-notarisation があり、b の全祖先を含む。

  ```lean
  def Finalised (f : Nat) (S : Finset (Msg n Tx)) (b : Block n Tx) : Prop :=
    LNotarised f S b ∧ ∀ a, Block.Ancestor a b → containsBlock S a
  ```

  - 初期の S で genesis はこれを満たし、「considered finalised at the start」に当たる。

- **処理内容**

  なし。31〜32 行の finalise を動作として持たず、S から定まる述語で表す。原文の log_i への反映は `log` が担う。

#### ■ Algorithm 1

- **原文**

  > We say ‘disseminate’ to mean ‘send to all processors’. When a correct processor is instructed to send a message to itself, it regards that message as immediately received.

  > ```
  >  1: At every timeslot t:
  >  2:   Disseminate new nullifications in S;                        ⊲ ‘new’ as defined in Section 4
  >  3:   Disseminate new M-notarisations in S;
  >  4:
  >  5:   If p_i = lead(v) and proposed = false:
  >  6:      ProposeChild(SelectParent(S, v), v);                             ⊲ Send out a new block
  >  7:      Set proposed := true;
  >  8:
  >  9:   If S contains a valid proposal b for view v:                      ⊲ As defined in Section 4
  > 10:      If notarised = ⊥ and nullified = false:
  > 11:         Set notarised := b and disseminate (vote, b);                            ⊲ Send vote
  > 12:
  > 13:   If T = 2Δ, nullified = false and notarised = ⊥:
  > 14:      Set nullified := true and disseminate (nullify, v);                   ⊲ Send nullify(v)
  > 15:
  > 16:   If S contains a nullification for v:
  > 17:      Set v := v + 1, nullified := false, proposed := false, notarised := ⊥, T := 0;
  > 18:                                                                         ⊲ Go to next view
  > 19:   If S contains an M-notarisation for some b with b.view = v:
  > 20:      If notarised = ⊥ and nullified = false, disseminate (vote, b);             ⊲ Send vote
  > 21:      Set v := v + 1, nullified := false, proposed := false, notarised := ⊥, T := 0;
  > 22:                                                                         ⊲ Go to next view
  > 23:
  > 24:   If nullified = false, notarised ≠ ⊥ and S contains ≥ 2f + 1 messages, each signed by a
  > 25:   different processor, and each either:
  > 26:    (i) A message (nullify, v), or;
  > 27:    (ii) Of the form (vote, b) for some b s.t. b.view = v and notarised ≠ b:
  > 28:       Set nullified := true and disseminate (nullify, v);
  > 29:                                  ⊲ Send nullify(v) message upon proof of no progress for v
  > 30:
  > 31:   If S contains a new L-notarisation for any block b:
  > 32:      Finalise b;                                  ⊲ Finalisation as specified in Section 2
  > ```

- **実装**

  ```lean
  noncomputable def stepPair (f Δ : Nat) (lead : View → Fin n) (i : Fin n) (p : Processor n Tx) :
      Processor n Tx × List (Action n Tx) :=
    let r₁ := climb f i (maxView p.S + 1) p
    let r₂ := propose f lead i r₁.1
    let r₃ := voteProposal f lead i r₂.1
    let r₄ := nullifyTimeout Δ i r₃.1
    let r₅ := nullifyNoProgress f i r₄.1
    let r₆ := forwardNew f i r₅.1
    (r₆.1, r₁.2 ++ r₂.2 ++ r₃.2 ++ r₄.2 ++ r₅.2 ++ r₆.2)
  ```

  - `stepPair` が疑似コードの全体で、局所状態から 1 スロット分の動作の列と、その後の局所状態を返す。`r₁` が 16〜21 行、`r₂` が 5〜7 行、`r₃` が 9〜11 行、`r₄` が 13〜14 行、`r₅` が 24〜28 行、`r₆` が 2〜3 行。論文の行順から、16〜21 行を先頭に、2〜3 行を最後尾に動かした。
  - 7・11・14・28 行のフラグの更新は `stepPair` には現れず、送信の動作の実行時に `Processor.send` が行う。
  - 17・21 行の view の更新も `stepPair` には現れず、前進の動作の実行時に `Processor.progress` が行う。
  - finalise は S 上の述語 `Finalised` として実装しているため、31〜32 行に当たる関数はない。

- **付属**

  - `step` : `stepPair` の動作の列だけを返す形
  - `step_eq_stepPair` : `step` が `stepPair` の動作の列に一致すること
  - `guardOK_step` : `step` の出力の各送信が、その時点の局所状態で送信のガードを通ること

## 3. 定理

### 3.1 仮定

遷移系が課さない規則で、定理の仮定になる。

#### ■ 初期状態

実行の初期状態を定める。

- **実装**

  ```lean
  structure Init [DecidableEq Tx] (s₀ : State n Tx) : Prop where
    procs : ∀ i, s₀.procs i = Processor.init
    byz : s₀.byz = ∅
    pool : s₀.pool = ∅
    now : s₀.now = ⟨0⟩
  ```

  - 全員が初期値 `Processor.init` で、誰も腐敗しておらず、何も送られておらず、スロット 0。

#### ■ プロトコルに従うこと

- **原文**

  > Algorithm 1: the instructions for p_i

- **実装**

  ```lean
  def Honest [DecidableEq Tx] (f Δ : Nat) (lead : View → Fin n) (s₀ : State n Tx)
      (instrs : Nat → Instr n Tx) : Prop :=
    ∀ t i, i ∉ (State.run s₀ instrs t).byz →
      (instrs t).actions i = Algo.step f Δ lead i ((State.run s₀ instrs t).procs i)
  ```

  - 全スロット t で、そのスロットの冒頭に腐敗していない p_i の動作が `Algo.step` の出力であること。腐敗したプロセッサの動作は制約を受けないが、送信のガードはかかる。

#### ■ 腐敗

- **原文**

  > For f such that 5f + 1 ≤ n, at most f processors may become corrupted by the adversary during the course of the execution … Processors that never become corrupted by the adversary are referred to as correct.

- **実装**

  ```lean
  def Correct [DecidableEq Tx] (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (i : Fin n) :
      Prop :=
    ∀ t, i ∉ (State.run s₀ instrs t).byz
  ```

  ```lean
  def ByzBound [DecidableEq Tx] (f : Nat) (s₀ : State n Tx) (instrs : Nat → Instr n Tx) :
      Prop :=
    ∀ t, (State.run s₀ instrs t).byz.card ≤ f
  ```

  - correct が `Correct`、f の上限が `ByzBound`。
  - 5f + 1 ≤ n は定理の仮定 hn で、Lemma 5.1 だけはこれを要しない。

#### ■ 部分同期

- **原文**

  > a message sent at time t must arrive at time t′ > t with t′ ≤ max{GST, t} + Δ. While Δ is known, the value of GST is unknown to the protocol.

- **実装**

  ```lean
  def State.Timely (Δ : Nat) (GST : Time) (s : State n Tx) : Prop :=
    ∀ x ∈ s.pool, max GST.val x.sentAt.val + Δ ≤ s.now.val → x.msg ∈ (s.procs x.dst).S
  ```

  ```lean
  structure PartialSync [DecidableEq Tx] (Δ : Nat) (GST : Time) (s₀ : State n Tx)
      (instrs : Nat → Instr n Tx) : Prop where
    timely : ∀ t, (State.run s₀ instrs t).Timely Δ GST
    one_le : 1 ≤ Δ
  ```

  - 1 つの状態で期限が守られていることが `Timely`、実行の全スロットでそれが成り立つことが `PartialSync`。
  - 各スロットの冒頭で、pool の packet のうち期限 max(GST, sentAt) + Δ に達したものは宛先の S にある。GST は定理の引数で任意の値をとる。t′ > t は、`instrs t` の受信がスロット t + 1 に入ることから自動的に満たされる。
  - `one_le` の Δ ≥ 1 は原文の条件から従う。GST 以後に送った message について、t′ > t と t′ ≤ t + Δ は Δ = 0 では両立しない。本形式化では受信の期限をスロット境界で判定するため、Δ = 0 でも実行が存在し、受信は次のスロットになる。一方 timeout は 2Δ = 0 なので、view に入ったスロットで、提案が届く前にリーダー以外の正直者が nullify を送り、リーダーのブロックは自分の票しか得ない。Lemma 5.6 が偽になるので、1 ≤ Δ を明示した。
  - Lemma 5.8〜5.10 の δ は、Lewis-Pye と Roughgarden の Permissionless Consensus 7.5 節の定義に合わせ、「t に送った message は max(GST, t) + δ までに届く」として `PartialSync δ GST` で置く。

#### ■ リーダー

- **原文**

  > The value lead(v) specifies the leader for view v. To be concrete, we set lead(v) := p_{j+1}, where j = v mod n.
  >
  > Of course, leaders can also be randomly selected, if given an appropriate source of common randomness.

- **実装**

  ```lean
  def Fair (lead : View → Fin n) : Prop :=
    ∀ i : Fin n, ∀ v : View, ∃ v' : View, v.val ≤ v'.val ∧ lead v' = i
  ```

  ```lean
  def CorrectLeaderWithin [DecidableEq Tx] (s₀ : State n Tx) (instrs : Nat → Instr n Tx)
      (lead : View → Fin n) (fa : Nat) : Prop :=
    ∀ v : View, ∃ v' : View, v.val ≤ v'.val ∧ v'.val ≤ v.val + fa ∧ Correct s₀ instrs (lead v')
  ```

  ```lean
  def roundRobin (hn : 0 < n) (v : View) : Fin n := ⟨v.val % n, Nat.mod_lt _ hn⟩
  ```

  ```lean
  theorem roundRobin_fair (hn : 0 < n) : Fair (roundRobin hn)
  ```

  ```lean
  theorem roundRobin_correct_leader {s₀ : State n Tx} {instrs : Nat → Instr n Tx} (hn : 0 < n)
      {fa : Nat} (hfa : fa + 1 ≤ n) (hb : ByzBound fa s₀ instrs) :
      CorrectLeaderWithin s₀ instrs (roundRobin hn) fa
  ```

  - lead に実装を与えず `View → Fin n` の引数にし、Lemma 5.7 では `Fair`、5.10 では `CorrectLeaderWithin` を仮定する。
  - §5 の証明が lead の具体形に依るのは、5.7 の「lead(v) = p_i となる v が GST 後にある」と 5.10 の「f_a + 1 個の連続する view に正直なリーダーがいる」の 2 箇所で、それぞれがこの 2 条件。原文の後半のとおり、選び方は固定でなくてよい。
  - `roundRobin` が原文の輪番で、添字を 0 始まりにした v mod n。
  - `roundRobin_fair` は輪番が `Fair` を満たすこと。
  - `roundRobin_correct_leader` は腐敗が fa 人以下なら、輪番が `CorrectLeaderWithin` を満たすこと。

#### ■ 充足可能性

定理の仮定が同時に満たせることを示す。

- **実装**

  ```lean
  theorem constraints_satisfiable (f Δ : Nat) (hΔ : 1 ≤ Δ) (lead : View → Fin n) :
      ∃ (s₀ : State n Tx) (instrs : Nat → Instr n Tx),
        Init s₀ ∧ Honest f Δ lead s₀ instrs ∧ ByzBound f s₀ instrs
          ∧ ∃ GST, PartialSync Δ GST s₀ instrs
  ```

  - Δ ≥ 1 なら、どの f と lead についても、`Init`・`Honest`・`ByzBound` と、ある GST についての `PartialSync` を同時に満たす s₀ と instrs がある。証人は、腐敗がなく、全員が `Algo.step` に従い、送った packet がそのスロットのうちに届く実行。

### 3.2 語彙

#### ■ sends と receives

- **原文**

  > We say block b receives an M-notarisation if b = b_gen or at least 2f + 1 processors send votes for b. Similarly, we say b receives an L-notarisation if b = b_gen or at least n − f processors send votes for b. View v receives a nullification if at least 2f + 1 processors send nullify(v) messages.

- **実装**

  ```lean
  def Sends (instrs : Nat → Instr n Tx) (i : Fin n) (m : Msg n Tx) : Prop :=
    ∃ t j, Action.send m j ∈ (instrs t).actions i
  ```

  ```lean
  def ReceivesM (f : Nat) (instrs : Nat → Instr n Tx) (b : Block n Tx) : Prop :=
    b = .gen ∨ 2 * f + 1 ≤ (voteSenders instrs b).card
  ```

  ```lean
  def ReceivesL (f : Nat) (instrs : Nat → Instr n Tx) (b : Block n Tx) : Prop :=
    b = .gen ∨ n - f ≤ (voteSenders instrs b).card
  ```

  ```lean
  def ReceivesNullification (f : Nat) (instrs : Nat → Instr n Tx) (v : View) : Prop :=
    2 * f + 1 ≤ (nullifySenders instrs v).card
  ```

  - sends が `Sends`。指示の列のどこかに、誰か宛に m を送る動作があること。ガードを通らない動作も含む。正直者の動作がガードを通ることは `guardOK_step` が示す。
  - receives の 3 つが `ReceivesM`・`ReceivesL`・`ReceivesNullification`。

- **付属**

  - `voteSenders` : b への自分の票を送ったプロセッサの集合、原文の「processors send votes for b」
  - `nullifySenders` : nullify(v) を送ったプロセッサの集合

#### ■ view への入場

論文は「enters view v」と「the first correct processor to enter view v does so at t」を定義せずに使っている。

- **実装**

  ```lean
  def Enters (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (i : Fin n) (v : View) (t : Nat) :
      Prop :=
    (viewAt s₀ instrs i t).val ≤ v.val ∧ v.val ≤ (viewAt s₀ instrs i (t + 1)).val
  ```

  ```lean
  structure FirstEntry (s₀ : State n Tx) (instrs : Nat → Instr n Tx) (v : View) (t : Nat) :
      Prop where
    entered : ∃ i, Correct s₀ instrs i ∧ Enters s₀ instrs i v t
    first : ∀ i t', Correct s₀ instrs i → Enters s₀ instrs i v t' → t ≤ t'
  ```

  - `Enters` は、スロット t の冒頭の view が v 以下で、スロット t + 1 の冒頭の view が v 以上であることを「t に v に入る」と読む。view は 1 回の前進で 1 しか増えないので、その間に view = v の時点がある。
  - `FirstEntry` の `entered` はスロット t に view v に入る正直者がいること、`first` はそれより前のスロットにはいないこと。

- **付属**

  - `viewAt` : スロット t の冒頭の p_i の view

#### ■ Tr*

- **原文**

  > Each block b thus naturally specifies an extended sequence of transactions, denoted b.Tr*, given by concatenating the values b′.Tr for all ancestors b′ of b, removing any duplicate transactions.

- **実装**

  ```lean
  def Block.trStar [DecidableEq Tx] : Block n Tx → List Tx
    | .gen => []
    | .node _ _ tr parent =>
      parent.trStar ++ (tr.filter fun x => decide (x ∉ parent.trStar)).eraseDups
  ```

#### ■ log と §2 の性質

- **原文**

  > We say σ and τ are compatible if σ ⪯ τ or τ ⪯ σ. … Each processor p_i is required to maintain an append-only log, denoted log_i, which at any timeslot is a sequence of distinct transactions. … The log being append-only means that for t′ > t, log_i(t) ⪯ log_i(t′). … Consistency. If p_i and p_j are correct, then for any timeslots t and t′, log_i(t) and log_j(t′) are compatible. Liveness. If p_i and p_j are correct and if p_i receives the transaction tr then, for some t, tr ∈ log_j(t).

- **実装**

  ```lean
  noncomputable def log (f : Nat) (S : Finset (Msg n Tx)) : List Tx :=
    match (finalisedBlocks f S).argmax Block.depth with
    | some b => b.trStar
    | none => []
  ```

  ```lean
  def Consistency (f : Nat) (s₀ : State n Tx) (instrs : Nat → Instr n Tx) : Prop :=
    ∀ i j, Correct s₀ instrs i → Correct s₀ instrs j → ∀ t t',
      log f ((State.run s₀ instrs t).procs i).S <+: log f ((State.run s₀ instrs t').procs j).S
      ∨ log f ((State.run s₀ instrs t').procs j).S <+: log f ((State.run s₀ instrs t).procs i).S
  ```

  ```lean
  def Liveness (f : Nat) (s₀ : State n Tx) (instrs : Nat → Instr n Tx) : Prop :=
    ∀ i j, Correct s₀ instrs i → Correct s₀ instrs j → ∀ t (tr : Tx),
      Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S →
      ∃ t', tr ∈ log f ((State.run s₀ instrs t').procs j).S
  ```

  - log_i は、原文では finalise が延長する変数で、本形式化では S から定まる関数にした。finalise したブロックは Lemma 5.4 により互いに祖先関係にあるので、最も深いものの Tr* が全部を延長する。
  - 追記のみであること log_i(t) ⪯ log_i(t′) は、S が増えるだけであることと `lnotarised_consistent` から従う。
  - `Consistency` と `Liveness` が原文の 2 性質で、compatible は `<+:` の選言。

- **付属**

  - `finalisedBlocks` : 票のあるブロックのうち `Finalised` なもの

### 3.3 定理文

各定理は「5f + 1 ≤ n と `Init s₀`・`Honest f Δ lead s₀ instrs`・`ByzBound f s₀ instrs` を満たす任意の s₀ と instrs について」の形をとる。仮定の名前は hn・hinit・hh・hb で、hb は hbz のこともある。以下ではこれらの説明を省く。Lemma 5.1 は `Init` と `Honest` だけを仮定する。Lemma 5.5〜5.7 は `PartialSync Δ GST s₀ instrs` を、5.7 は `Fair lead` も仮定する。5.8〜5.10 は δ ≤ Δ をとって `PartialSync δ GST s₀ instrs` を仮定し、5.10 はさらに `CorrectLeaderWithin` を仮定する。「正直者 p_i」は `Correct s₀ instrs i`。論文の view は ℕ≥1 なので、view v についての Lemma 5.6・5.8・5.9 は 1 ≤ v を仮定に持つ。

#### ■ Lemma 5.1 (One vote per view)

- **原文**

  > Correct processors vote for at most one block in each view, i.e., if p_i is correct then, for each v ∈ N≥1, there exists at most one b with b.view = v such that p_i sends a message (vote, b).

- **実装**

  ```lean
  theorem one_vote_per_view (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i)
      {b b' : Block n Tx} (hb : Sends instrs i (.vote i b)) (hb' : Sends instrs i (.vote i b'))
      (hview : b.view = b'.view) : b = b'
  ```

#### ■ Lemma 5.2 ((X1) is satisfied)

- **原文**

  > If b receives an L-notarisation, then no block b′ ≠ b with b′.view = b.view receives an M-notarisation.

- **実装**

  ```lean
  theorem receivesM_unique_of_receivesL (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
      {b b' : Block n Tx} (hL : ReceivesL f instrs b) (hview : b'.view = b.view)
      (hM : ReceivesM f instrs b') : b' = b
  ```

#### ■ Lemma 5.3 ((X2) is satisfied)

- **原文**

  > If b receives an L-notarisation and v = b.view, then view v does not receive a nullification.

- **実装**

  ```lean
  theorem not_receivesNullification_of_receivesL (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
      {b : Block n Tx} (hL : ReceivesL f instrs b) : ¬ ReceivesNullification f instrs b.view
  ```

#### ■ Lemma 5.4 (Consistency)

- **原文**

  > The protocol satisfies Consistency.
  >
  > Two blocks are inconsistent if neither is an ancestor of the other. … Towards a contradiction, suppose that two inconsistent blocks, b and b′ say, both receive L-notarisations.

- **実装**

  ```lean
  theorem consistency (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hbz : ByzBound f s₀ instrs) : Consistency f s₀ instrs
  ```

  ```lean
  theorem receivesL_consistent (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
      {b b' : Block n Tx} (hL : ReceivesL f instrs b) (hL' : ReceivesL f instrs b') :
      b.Ancestor b' ∨ b'.Ancestor b
  ```

  ```lean
  theorem lnotarised_consistent (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
      {i j : Fin n} {t t' : Nat} {b b' : Block n Tx}
      (hbi : LNotarised f ((State.run s₀ instrs t).procs i).S b)
      (hbj : LNotarised f ((State.run s₀ instrs t').procs j).S b') :
      b.Ancestor b' ∨ b'.Ancestor b
  ```

  - 証明の本体は補題 `receivesL_consistent` で、原文の背理法の仮定が成り立たないこと、すなわち L-notarisation を受けた 2 つのブロックは inconsistent でないことを、共通の仮定だけから示す。それを 2 つのプロセッサの S にある L-notarisation の形にしたのが `lnotarised_consistent` で、Lemma 5.4 はこれと log の定義から従う。

#### ■ Lemma 5.5 (Progression through views)

- **原文**

  > Every correct processor enters every view v ∈ N≥1.

- **実装**

  ```lean
  theorem progression (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
      (hs : PartialSync Δ GST s₀ instrs) {i : Fin n} (hi : Correct s₀ instrs i) {v : View}
      (hv : 1 ≤ v.val) : ∃ t, Enters s₀ instrs i v t
  ```

#### ■ Lemma 5.6 (Correct leaders finalise blocks)

- **原文**

  > If p_i = lead(v) is correct, and if the first correct processor to enter view v does so after GST, then p_i disseminates a block and that block receives an L-notarisation.

- **実装**

  ```lean
  theorem correct_leader_finalises (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
      (hs : PartialSync Δ GST s₀ instrs) {v : View} (hv : 1 ≤ v.val) (hi : Correct s₀ instrs (lead v))
      {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : GST.val ≤ t) :
      ∃ b : Block n Tx, b.view = v ∧ b.signer = some (lead v)
        ∧ (∃ t', ∀ j, Action.send (.propose b) j ∈ (instrs t').actions (lead v))
        ∧ ReceivesL f instrs b
  ```

  - 結論の b は lead(v) の署名付きの view v のブロックで、あるスロットに lead(v) が全員へ `propose b` を送り、b は L-notarisation を受ける。

#### ■ Lemma 5.7 (Liveness)

- **原文**

  > The protocol satisfies Liveness.

- **実装**

  ```lean
  theorem liveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hbz : ByzBound f s₀ instrs)
      (hs : PartialSync Δ GST s₀ instrs) (hlead : Fair lead) : Liveness f s₀ instrs
  ```

  ```lean
  theorem tx_finalised (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
      (hs : PartialSync Δ GST s₀ instrs) (hlead : Fair lead)
      {i j : Fin n} (hi : Correct s₀ instrs i)
      {t : Nat} {tr : Tx} (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S) :
      ∃ t' b, Finalised f ((State.run s₀ instrs t').procs j).S b ∧ tr ∈ b.trStar
  ```

  - 証明の本体は補題 `tx_finalised` で、正直者 p_i が受け取った取引が、あるスロットに p_j が finalise したブロックの Tr* に入ることを、p_j の正直さを仮定せずに示す。`PartialSync` が保証する受信は宛先の正直さによらない。Lemma 5.7 はこれと log の定義から従う。

#### ■ Lemma 5.8

- **原文**

  > Suppose lead(v) is correct and that the first correct processor to enter view v does so at t ≥ GST. Then all correct processors leave view v and finalise a view v block by t + O(δ).
  >
  > All correct processors therefore receive b together with an L-notarisation (and an M-notarisation) for b by t + 3δ, and also leave view v by this time.

- **実装**

  ```lean
  theorem correct_leader_finalises_fast (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
      (hδ : δ ≤ Δ) (hs : PartialSync δ GST s₀ instrs) {v : View} (hv : 1 ≤ v.val)
      (hi : Correct s₀ instrs (lead v))
      {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : GST.val ≤ t) :
      ∀ j, Correct s₀ instrs j →
        (∃ b : Block n Tx, b.view = v ∧ Finalised f ((State.run s₀ instrs (t + 3 * δ)).procs j).S b)
        ∧ v.val < (viewAt s₀ instrs j (t + 3 * δ + 1)).val
  ```

  - O(δ) は原文の証明の 3δ。結論の前半は t + 3δ の冒頭までに view v のブロックを finalise していること、後半は t + 3δ + 1 の冒頭には view v を離れていること。

#### ■ Lemma 5.9

- **原文**

  > Suppose the first correct processor to enter view v does so at t ≥ GST. Then, whether or not lead(v) is correct, all correct processors leave view v by t + O(Δ).
  >
  > Towards a contradiction, suppose some correct processor does not leave view v by t + 2Δ + 3δ.

- **実装**

  ```lean
  theorem leave_view (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
      (hδ : δ ≤ Δ) (hs : PartialSync δ GST s₀ instrs) {v : View} (hv : 1 ≤ v.val)
      {t : Nat} (hfirst : FirstEntry s₀ instrs v t) (hgst : GST.val ≤ t) :
      ∀ j, Correct s₀ instrs j → v.val < (viewAt s₀ instrs j (t + 2 * Δ + 3 * δ + 1)).val
  ```

  - O(Δ) は原文の証明の 2Δ + 3δ。

#### ■ Lemma 5.10

- **原文**

  > Let δ ≤ Δ be the actual (unknown) least upper bound on message delay after GST, and let f_a ≤ f be the actual (unknown) number of Byzantine processors. If a transaction tr is first received by a correct processor at time t, and is first finalised by all correct processors (i.e., appended to log_i for every correct p_i) at time t + ℓ, then we say latency for tr is ℓ. We say a protocol is optimistically responsive if latency is O(f_a Δ + δ) for all transactions that are first received by any correct processor after GST
  >
  > Minimmit is optimistically responsive.

- **実装**

  ```lean
  theorem optimistic_responsiveness (hn : 5 * f + 1 ≤ n) (hinit : Init s₀)
      (hh : Honest f Δ lead s₀ instrs) (hb : ByzBound f s₀ instrs)
      (hδ : δ ≤ Δ) (hs : PartialSync δ GST s₀ instrs) {fa : Nat}
      (hlead : CorrectLeaderWithin s₀ instrs lead fa)
      {i : Fin n} (hi : Correct s₀ instrs i) {t : Nat} {tr : Tx}
      (htr : Msg.tx tr ∈ ((State.run s₀ instrs t).procs i).S)
      (hfirst : ∀ j t', Correct s₀ instrs j → t' < t →
        Msg.tx tr ∉ ((State.run s₀ instrs t').procs j).S)
      (hgst : GST.val ≤ t) :
      ∀ j, Correct s₀ instrs j → ∃ b : Block n Tx,
        Finalised f ((State.run s₀ instrs (t + δ + (fa + 1) * (2 * Δ + 3 * δ) + 3 * δ)).procs j).S b
        ∧ tr ∈ b.trStar
  ```

  - δ は `PartialSync δ GST` で置く。`hfirst` は、取引 tr を正直者が初めて受け取るのが t であること。
  - t + δ + (f_a + 1)(2Δ + 3δ) + 3δ は、取引が全員に届く t + δ に、5.9 を f_a + 1 view 分と 5.8 を足したもので、論文の O(f_a Δ + δ)。

## 4. 対応の外

論文の §3 の直観、§6 の最適化、§7 の実験、付録は対象外。

暗号は論文と同じく理想化する。署名は署名者の成分と送信のガード、ハッシュは親の実体参照で表し、確率的な議論は無い。論文でも暗号を破る実行は考えないとしているので、これは差異ではない。

スロット遷移の項で述べた、スロット内の動作の順序の固定について、tick と tick の間で原始関数がどの順に並んでも同じ状態に至ること、この固定順で表せない挙動が「送ったスロットの中での受信」だけであることは、可換性による形式化の外の議論に依っていて未証明。

## 5. 参考

- 論文: Brendan Kobayashi Chou, Andrew Lewis-Pye, Patrick O'Grady, "Minimmit: Fast Finality with Even Faster Blocks", [arXiv:2508.10862](https://arxiv.org/abs/2508.10862)。基準は v7（2026-01-27）、CC BY 4.0。引用は同論文から。
- δ の定義: Andrew Lewis-Pye, Tim Roughgarden, "Permissionless Consensus", [arXiv:2304.14701](https://arxiv.org/abs/2304.14701)、7.5 節。
- 実装の仕様書: Commonware の [minimmit.md](https://github.com/commonwarexyz/monorepo/blob/4ff08da00068d61d50f745be2942d6a45597ed46/pipeline/minimmit/minimmit.md)（monorepo、2026-01-22 時点、Apache-2.0 と MIT）。論文の Algorithm 1 でなく実装の仕様で、「On 発動条件: 処理内容」の形で書かれている。
