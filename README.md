# minimmit-lean

BFT コンセンサスプロトコル Minimmit（Chou et al., [arXiv:2508.10862](https://arxiv.org/abs/2508.10862)）の Lean 4 による形式化。論文 §4 の Algorithm 1 を実行モデルの上で関数として定義し、§5 の Lemma 5.1〜5.10 を証明する。

学習のための自前の形式化で、[NyxFoundation/minimmit-fv](https://github.com/NyxFoundation/minimmit-fv) とは独立に作った。minimmit-fv はプロトコルの性質を仮定の構造体に切り出して補題を導くのに対し、ここでは状態遷移とアルゴリズムを具体的に定義し、補題はその実行について証明する。

## 状態

Lemma 5.1〜5.10 はすべて証明済み。`sorry` はなく、各定理が依存する公理は `propext`・`Classical.choice`・`Quot.sound` のみ。

| 論文 | 定理 | ファイル |
|---|---|---|
| Lemma 5.1 One vote per view | `one_vote_per_view` | Analysis/Consistency/Lemma5_1 |
| Lemma 5.2 (X1) | `x1` | Analysis/Consistency/Lemma5_2 |
| Lemma 5.3 (X2) | `x2` | Analysis/Consistency/Lemma5_3 |
| Lemma 5.4 Consistency | `finalised_compatible`, `consistency` | Analysis/Consistency/Lemma5_4 |
| Lemma 5.5 Progression through views | `progression` | Analysis/Liveness/Lemma5_5 |
| Lemma 5.6 Correct leaders finalise blocks | `correct_leader_finalises` | Analysis/Liveness/Lemma5_6 |
| Lemma 5.7 Liveness | `liveness` | Analysis/Liveness/Lemma5_7 |
| Lemma 5.8 | `correct_leader_finalises_fast` | Analysis/Responsiveness/Lemma5_8 |
| Lemma 5.9 | `leave_view` | Analysis/Responsiveness/Lemma5_9 |
| Lemma 5.10 Optimistic responsiveness | `optimistic_responsiveness` | Analysis/Responsiveness/Lemma5_10 |

## ビルド

Lean `v4.29.1`、Mathlib `v4.29.1`。

```
lake exe cache get
lake build
```

## モデル

定義は `Model/` の 4 つの `Basic.lean` にある。論文と突き合わせるには Transition、Certificate、Algo、Constraint の順に読む。以下は論文の概念と Lean の定義の対応。

### 実行モデル（§2）

時間は離散のスロット。各スロットで、各プロセッサが動作の列を起こし、次に網から message が届き、取引が投入され、腐敗が起きる。この 1 スロット分を `Instr` が指定し、`State.step` が状態に適用する。

| 論文 | Lean | 備考 |
|---|---|---|
| スロット t の状態 | `State.run s₀ instrs t` | スロット t の冒頭の状態。t の動作で起きた view の変化は t + 1 の冒頭に現れる |
| 実行 | `instrs : Nat → Instr` | 各スロットの動作列 `actions`・配送 `deliveries`・取引投入 `submits`・腐敗 `corrupts`。定理はこの列を任意に取るので、敵対者の選択はすべてここに入る |
| プロセッサの動作 | `Action` | message を誰かへ送る `send`、次の view へ進む `progress` |
| 網 | `State.pool`、`Packet` | packet は message・宛先・送信スロットの組。送った packet は `pool` に載り、`pool` にあるものだけが届く |
| 署名の偽造不能 | `State.send` のガード | 自分の署名付きか受信済みの message だけ送れる |
| 腐敗 | `State.byz` | 腐敗したプロセッサの集合。増えるだけで減らない |

### プロセッサと message（§4）

| 論文 | Lean | 備考 |
|---|---|---|
| Table 2 の view、T、nullified、proposed、notarised、S | `Processor` の `view`、`timer`、`nullified`、`proposed`、`notarised`、`S` | notarised の ⊥ は `none` |
| なし | `Processor.prevS` | 前スロットの動作を終えた時点の S。2〜3 行の「new」の判定に使う |
| ブロック | `Block` | genesis `gen` か、view・取引列・親の組 `node` |
| Tr* | `Block.trStar` | b とその祖先の取引列を古い順に連結したもの |
| 提案・票・nullify・取引 | `Msg` の `block`・`vote`・`nullify`・`tx` | 前の 3 つは署名者 `q` を持つ。取引は署名を持たない |

### 証明書（§4、§5.1）

§4 の証明書は message の集合 S 上の述語。§5.1 の「b が M-notarisation を受ける」は、誰かの S でなく実行の中で誰が何を送ったかで言う述語。

| 論文 | Lean | 備考 |
|---|---|---|
| S にある b の M-notarisation | `MNotarised f S b` | 相異なる 2f + 1 人の票。genesis は無条件に認める |
| S にある b の L-notarisation | `LNotarised f S b` | 相異なる n − f 人の票。genesis は無条件に認める |
| S にある view v の nullification | `Nullified f S v` | 相異なる 2f + 1 人の nullify(v) |
| valid proposal | `ValidProposal f lead S v b` | 条件 (i)〜(iii) をフィールドに持つ構造体 |
| proof of no progress | `NoProgress f S v notarised` | 24〜27 行の条件。2f + 1 人のそれぞれが、nullify(v) を送ったか、notarised 以外の view v のブロックに投票した |
| p_i が m を送る | `Sends instrs i m` | 指示の列のどこかに m を送る動作がある |
| b が M-notarisation を受ける | `ReceivesM f instrs b` | 2f + 1 人が b に票を送った。L-notarisation は `ReceivesL`、nullification は `ReceivesNullification` |

### Algorithm 1（§4）

`Algo.step f Δ lead i p` が、p_i の局所状態 p から 1 スロット分の動作列を返す。行の対応は次のとおり。評価順は論文と異なり、[論文からの差異](#論文からの差異) に書く。

| Algorithm 1 | Lean |
|---|---|
| 2〜3 行 新しい証明書の転送 | `forwardNew` |
| 5〜7 行 SelectParent、ProposeChild | `selectParent`、`payload` |
| 9〜11 行 投票 | `step` の中。提案の列挙は `proposals`、条件は `ValidProposal` |
| 13〜14 行 timeout の nullify | `step` の中 |
| 16〜21 行 view の前進 | `advanceOnce`、`climb` |
| 24〜28 行 進捗のなさの nullify | `step` の中。条件は `NoProgress` |
| 31〜32 行 Finalise | 動作なし。finalise したことは S に L-notarisation があることで表す |

### 仮定と定理（§2、§5）

論文の仮定は、遷移系が課さない制約として定義し、定理の仮定に置く。

| 論文 | Lean | 備考 |
|---|---|---|
| n ≥ 5f + 1 | `5 * f + 1 ≤ n` | 定理の仮定 |
| Table 2 の初期値 | `Init s₀` | 全プロセッサが `Processor.init`、byz と pool は空、now は 0 |
| 正直者は Algorithm 1 に従う | `Honest f Δ lead s₀ instrs` | 各スロットで byz にないプロセッサの動作列は `Algo.step` の出力 |
| 腐敗は高々 f 人 | `ByzBound f s₀ instrs` | 全スロットで byz の要素数が f 以下 |
| 部分同期 | `PartialSync Δ s₀ instrs` | GST は構造体のフィールド。t に送った packet は max(GST, t) + Δ までに届く。Δ ≥ 1 |
| lead の輪番 | `Fair lead` | どのプロセッサも、どの view 以降にも自分がリーダーになる view を持つ |
| correct processor | `Correct s₀ instrs i` | 全スロットで byz にない |

定理は「`Init s₀`、`Honest`、`ByzBound f` を満たす任意の `s₀` と `instrs` について」の形で述べる。Lemma 5.5 以降はさらに `PartialSync Δ` を、Lemma 5.7 は `Fair lead` を仮定する。たとえば `consistency` は、任意のプロセッサ i, j と任意のスロット t, t′ について、i の S に b の L-notarisation があり j の S に b′ の L-notarisation があれば、b と b′ の一方が他方の祖先であると述べる。

## ファイル構成

`Model/` が §4、`Analysis/` が §5。`Model/` の各ディレクトリでは `Basic.lean` が定義で、他のファイルは補題。

```
Minimmit
├── Model
│   ├── Transition
│   │   ├── Basic.lean          状態、message、原始関数（send・progress・deliver・submit・corrupt）、State.step、State.run
│   │   └── Execute.lean        原始関数の局所効果、動作列の畳み込み、1 スロット後の状態との関係
│   ├── Certificate
│   │   ├── Basic.lean          §4 の述語（M/L-notarisation、nullification、valid proposal、proof of no progress）
│   │   └── Mono.lean           述語の単調性、投票者・nullify 送信者の集合
│   ├── Algo
│   │   ├── Basic.lean          Algorithm 1（Algo.step）と部品（SelectParent、ProposeChild、転送、登り）
│   │   ├── Disseminate.lean    全員への送信の補題
│   │   ├── Stage.lean          Algo.step の段ごとの分解、各段の入力状態 st1〜st5、各段の S と view
│   │   ├── LocalInv.lean       局所不変量（LocalInv・PropInv）と各段での保存
│   │   ├── Climb.lean          登り（16〜21 行の繰り返し）の補題
│   │   ├── Send.lean           各段の S の中身、各段が送る message とその条件、票と nullify の出所
│   │   └── Forward.lean        転送と反応の補題、SelectParent と valid proposal
│   └── Constraint
│       ├── Basic.lean          Init、PartialSync、Correct、ByzBound、Fair、Honest
│       └── Run.lean            署名の遡り（S にあれば署名者が前に送った）、腐敗の数え上げ、不変量の実行への持ち上げ
└── Analysis
    ├── Consistency
    │   ├── Lemma5_1.lean
    │   ├── Lemma5_2.lean
    │   ├── Lemma5_3.lean
    │   └── Lemma5_4.lean
    ├── Liveness
    │   ├── Timing.lean         view と timer の推移、部分同期による配送、証明書の転送、証明書への反応
    │   ├── Lemma5_5.lean
    │   ├── LeaderRound.lean    Lemma 5.6 の補題群
    │   ├── Lemma5_6.lean
    │   └── Lemma5_7.lean
    └── Responsiveness
        ├── Lemma5_8.lean
        ├── Lemma5_9.lean
        └── Lemma5_10.lean
```

## 論文からの差異

形式化は論文と次の点で異なる。定理は、これらの差異を含んだプロトコルについて成り立つ。各差異の理由と、論文との関係を示す定理は、所在ファイルの冒頭の doc に「論文からの差異」として書いてある。

### 擬似コードの修正

論文の擬似コードは、論文の証明が使う動作をしていない。登り切りがないと Lemma E.6 が偽になり、行順のままだと証明の時間計算が 1〜2 スロットずれる。

| 差異 | 論文との関係 | 所在 |
|---|---|---|
| Algorithm 1 を 16〜21、5〜7、9〜11、13〜14、24〜28、2〜3 行の順に評価する | 証明の時間計算どおりになる。行順でも O(·) の主張は偽にならず、ずれは定数 | Model/Algo/Basic |
| 16〜21 行を、現在の view の証明書がある限り繰り返す | 1 回評価では Lemma E.6 が偽になる実行がある | Model/Algo/Basic |

### 具体化と同値な符号化

| 差異 | 論文との関係 | 所在 |
|---|---|---|
| ブロックは親をハッシュでなくブロックそのもので持つ | 暗号を完全と仮定する論文では区別できない | Model/Transition/Basic |
| Tr* の重複を除去しない | Lemma 5.7 の結論は重複に依らない | Model/Transition/Basic |
| 初期状態の S は空。genesis の M/L-notarisation は述語が無条件に認める | 述語の値が同じ | Model/Certificate/Basic |
| 2〜3 行の転送で、証明書を構成する message を S にある分すべて送る | 各宛先が受け取る集合が論文の上位集合 | Model/Algo/Basic |
| 「some b」や同点の選択は S の列挙順 | 論文が任意に残した選択の一例 | Model/Algo/Basic |
| finalise は動作を伴わない。S に L-notarisation があることで表す | 31 行の条件そのもの | Model/Algo/Basic |
| 配送の期限はスロット境界で判定する | 同じ期限をスロット冒頭で述べたもの | Model/Constraint/Basic |
| Δ ≥ 1 を `PartialSync` に明示する | 論文の仮定から従う | Model/Constraint/Basic |
| lead は輪番に固定せず任意の関数。Lemma 5.7 は `Fair` を仮定する | 論文の輪番は `Fair` を満たす | Model/Constraint/Basic |
| Lemma 5.8〜5.10 の δ は `PartialSync δ` として与える | GST 後の実際の遅延を Δ の代わりに置いたもの | Analysis/Responsiveness/Lemma5_8 |

### ステートメントの精密化

| 差異 | 論文との関係 | 所在 |
|---|---|---|
| Lemma 5.5 の「view v に入る」を「view v 以上に達する」と述べる | view は 1 ずつ進むので同値 | Analysis/Liveness/Lemma5_5 |
| Lemma 5.6・5.8・5.9 は view v ≥ 1 を仮定に持つ | 論文の view の範囲 ℕ≥1 を明示したもの | 各 Lemma のファイル |
| Lemma 5.4 の `consistency` は p_i・p_j の正直さを仮定しない | 論文の主張を含む | Analysis/Consistency/Lemma5_4 |
| Lemma 5.8〜5.10 の O(·) を具体的な上界に置き換える | 具体的な上界は O(·) の主張を含む | Analysis/Responsiveness の各ファイル |
| Lemma 5.10 のリーダー条件は「どの f_a + 1 個の連続する view にも正直なリーダーがいる」 | 論文の輪番はこれを満たすので、論文の設定を含む | Analysis/Responsiveness/Lemma5_10 |

## 未証明

- スロット内の動作の順序を固定している。tick と tick の間で原始関数がどの順に並んでも同じ状態に至ること、この固定順で表せない挙動が「送ったスロットの中で届く配送」だけであることは、形式化の外の議論に依っていて未証明。
