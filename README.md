# minimmit-lean

BFT コンセンサスプロトコル Minimmit（Chou et al., [arXiv:2508.10862](https://arxiv.org/abs/2508.10862)）の Lean 4 による形式化。論文 §4 の Algorithm 1 を実行モデルの上で関数として定義し、§5 の Lemma 5.1〜5.10 を証明する。

学習のための自前の形式化で、[NyxFoundation/minimmit-fv](https://github.com/NyxFoundation/minimmit-fv) とは独立に作った。minimmit-fv はプロトコルの性質を仮定の構造体に切り出して補題を導くのに対し、ここでは状態遷移とアルゴリズムを具体的に定義し、補題はその実行について証明する。

## 状態

Lemma 5.1〜5.10 はすべて証明済み。`sorry` はなく、各定理が依存する公理は `propext`・`Classical.choice`・`Quot.sound` のみ。`Minimmit/Axioms.lean` が主定理ごとにこれを `#guard_msgs` で固定し、GitHub Actions の CI が push ごとにビルドと、ライブラリ全体の公理の監査を回す。

| 論文 | 定理 | ファイル |
|---|---|---|
| Lemma 5.1 One vote per view | `one_vote_per_view` | Analysis/Consistency/Lemma5_1 |
| Lemma 5.2 (X1) | `receivesM_unique_of_receivesL` | Analysis/Consistency/Lemma5_2 |
| Lemma 5.3 (X2) | `not_receivesNullification_of_receivesL` | Analysis/Consistency/Lemma5_3 |
| Lemma 5.4 Consistency | `satisfies_consistency`, `consistency`, `finalised_compatible` | Analysis/Log, Analysis/Consistency/Lemma5_4 |
| Lemma 5.5 Progression through views | `progression` | Analysis/Liveness/Lemma5_5 |
| Lemma 5.6 Correct leaders finalise blocks | `correct_leader_finalises` | Analysis/Liveness/Lemma5_6 |
| Lemma 5.7 Liveness | `satisfies_liveness`, `liveness` | Analysis/Log, Analysis/Liveness/Lemma5_7 |
| Lemma 5.8 | `correct_leader_finalises_fast` | Analysis/Responsiveness/Lemma5_8 |
| Lemma 5.9 | `leave_view` | Analysis/Responsiveness/Lemma5_9 |
| Lemma 5.10 Optimistic responsiveness | `optimistic_responsiveness` | Analysis/Responsiveness/Lemma5_10 |

Lemma 5.4 と 5.7 は、§2 の Consistency・Liveness の定義（正直者の log について）を `satisfies_consistency`・`satisfies_liveness` として証明する。`consistency`・`liveness` はそれをブロックの形で述べたもので、p_i・p_j の正直さを仮定しない。`finalised_compatible` は、実行上で L-notarisation を受けた 2 つのブロックについて述べる。

## ビルド

Lean `v4.29.1`、Mathlib `v4.29.1`。

```
lake exe cache get
lake build
```

定理はすべて名前空間 `Minimmit` にある。依存公理は次で確認できる。

```
printf 'import Minimmit\n#print axioms Minimmit.liveness\n' | lake env lean --stdin
```

## モデル

定義は `Model/` の 4 つの `Basic.lean` にある。Transition が遷移系、Certificate が証明書、Algo が Algorithm 1、Constraint が仮定。

### 遷移系

時間は離散のスロット。大域状態 `State` は、各プロセッサの局所状態 `Processor`、ネットワーク、腐敗集合からなる。1 スロットに起きること、つまり各プロセッサの動作列・配送・取引投入・腐敗を `Instr` が指定し、`State.step` が適用する。実行は初期状態 `s₀` と指示の列 `instrs` で決まり、`State.run s₀ instrs t` がスロット t の冒頭の状態。敵対者の選択はすべて `instrs` に入る。

### アルゴリズムと証明書

`Algo.step` が Algorithm 1 で、局所状態から 1 スロット分の動作列を返す。M/L-notarisation などの証明書は、message の集合 S 上の述語。finalise したこと、つまり S に L-notarisation があり全祖先を含むことは `Finalised`。log は `Analysis/Log` の `log` で、S から定まる。

### 仮定と定理

論文の仮定は制約として定義し、定理の仮定に置く。`Init` は初期状態、`Honest` は正直者の動作列が `Algo.step` の出力であること、`ByzBound` は腐敗が f 人以下、`PartialSync` は部分同期、`Fair` はリーダー関数の公平性。`Correct i` は p_i が全スロットで腐敗集合にないことで、定理の中の「正直者 p_i」はこれで述べる。定理は「n ≥ 5f + 1 と `Init`・`Honest`・`ByzBound` を満たす任意の `s₀` と `instrs` について」の形で、Lemma 5.5〜5.7 は `PartialSync Δ` を、Lemma 5.7 は `Fair` も仮定する。Lemma 5.8〜5.10 は GST 後の実際の遅延 δ ≤ Δ をとって `PartialSync δ` を仮定し、Lemma 5.10 はさらに `CorrectLeaderWithin`、つまりどの f_a + 1 個の連続する view にも正直なリーダーがいることを仮定する。4 つの制約が同時に満たせることは Constraint/Witness の `constraints_satisfiable` が示す。

## 論文との対応

論文の概念がどの定義に当たるか。定義の意味は各定義の docstring にある。

### §2 のモデル

| 論文 | Lean |
|---|---|
| タイムスロット、現在時刻 | `Time`、`State.now`、`State.run` |
| プロセッサ、腐敗 | `Processor`、`State.byz`、`Instr.corrupts`、`Correct`、`ByzBound` |
| 署名の偽造不能 | `Block.signer`・`Msg.signer` と `State.send` のガード `Processor.canSend` |
| 部分同期（GST、Δ） | `PartialSync`、`State.Timely` |
| 取引 | `Msg.tx`、`Instr.submits` |
| log、finalise | `log`（S の関数）、`Finalised` |
| Consistency、Liveness | `Consistency`、`Liveness`、`satisfies_consistency`、`satisfies_liveness` |

### §4 の用語

| 論文 | Lean |
|---|---|
| block、genesis | `Block`（親は実体）、`Block.gen` |
| vote、nullify(v) | `Msg.vote`、`Msg.nullify` |
| M-notarisation、L-notarisation、nullification | `MNotarised`、`LNotarised`、`Nullified` |
| S、v、T | `Processor.S`、`Processor.view`、`Processor.timer` |
| Table 2 の初期値 | `Processor.init`、初期の S は `genesisS` |
| nullified、proposed、notarised | `Processor` の同名フィールド |
| lead | `lead` 引数、`Fair`、`roundRobin` |
| SelectParent、ProposeChild | `selectParent`、`payload`・`propose`、送る message は `Msg.propose` |
| valid proposal、proof of no progress | `ValidProposal`、`NoProgress` |
| new nullification / notarisation | `forwardNew`（S にあって prevS にないもの） |
| Tr* | `Block.trStar` |
| disseminate | `disseminate` |
| §5.1 の receives、sends | `ReceivesM`・`ReceivesL`・`ReceivesNullification`、`Sends` |
| §5 の「view v に入る」 | `Enters`、最初の正直者の入場は `FirstEntry` |

### Algorithm 1

| 行 | Lean |
|---|---|
| 2〜3 | `forwardMsgs` |
| 5〜7 | `propose` |
| 9〜11 | `voteProposal` |
| 13〜14 | `nullifyTimeout` |
| 16〜21 | `advanceOnce`、`climb` |
| 24〜28 | `nullifyNoProgress` |
| 31〜32 | 動作なし。`LNotarised` が S にあること |
| 全体と評価順 | `Algo.step`、順序は Algo/Basic の doc |

## ファイル構成

`Model/` が §4、`Analysis/` が §5。`Model/` の各ディレクトリでは `Basic.lean` が定義で、他のファイルは補題。

```
Minimmit
├── Axioms.lean             主定理の一覧と、依存公理の固定
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
│       ├── Run.lean            署名の遡り（S にあれば署名者が前に送った）、腐敗の数え上げ、不変量の実行への持ち上げ
│       └── Witness.lean        Init・Honest・ByzBound・PartialSync を同時に満たす実行の例、輪番の lead が Fair と 5.10 のリーダーの仮定を満たすこと
└── Analysis
    ├── Log.lean                log と、§2 の Consistency・Liveness
    ├── Consistency
    │   ├── Lemma5_1.lean
    │   ├── Lemma5_2.lean
    │   ├── Lemma5_3.lean
    │   └── Lemma5_4.lean
    ├── Liveness
    │   ├── Timing.lean         view と timer の推移、部分同期による配送、証明書の転送、証明書への反応
    │   ├── Lemma5_5.lean
    │   ├── LeaderRound.lean    Lemma 5.6 の補題群
    │   ├── Finalise.lean       確定と祖先の到着
    │   ├── Lemma5_6.lean
    │   └── Lemma5_7.lean
    └── Responsiveness
        ├── Lemma5_8.lean
        ├── Lemma5_9.lean
        └── Lemma5_10.lean
```

## 形式化の注記

論文からの差異とその理由は [NOTES.md](NOTES.md) にまとめてある。Algorithm 1 は、証明書が届いている限り同じスロットで view を進め続けることと、view を進めてから提案と投票をし転送をスロットの最後に回すことの 2 点で論文の擬似コードと違い、論文の証明はどちらの動作も前提にしている。そのほかの差異は論文の記述を Lean に落とすための調整で、該当ファイルの冒頭の doc に「論文からの差異」として理由つきで書いてある。スロット内の動作の順序を固定していることが挙動を狭めないことは、形式化の外の議論に依っていて未証明。
