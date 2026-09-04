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

Lemma 5.4 の `finalised_compatible` は、実行上で L-notarisation を受けた 2 つのブロックについて述べ、`consistency` はそれを 2 つのプロセッサの S にある L-notarisation の形で述べたもの。

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

`Algo.step` が Algorithm 1 で、局所状態から 1 スロット分の動作列を返す。M/L-notarisation などの証明書は、message の集合 S 上の述語。

### 仮定と定理

論文の仮定は制約として定義し、定理の仮定に置く。`Init` は初期状態、`Honest` は正直者の動作列が `Algo.step` の出力であること、`ByzBound` は腐敗が f 人以下、`PartialSync` は部分同期、`Fair` はリーダー関数の公平性。`Correct i` は p_i が全スロットで腐敗集合にないことで、定理の中の「正直者 p_i」はこれで述べる。定理は「n ≥ 5f + 1 と `Init`・`Honest`・`ByzBound` を満たす任意の `s₀` と `instrs` について」の形で、Lemma 5.5〜5.7 は `PartialSync Δ` を、Lemma 5.7 は `Fair` も仮定する。Lemma 5.8〜5.10 は GST 後の実際の遅延 δ ≤ Δ をとって `PartialSync δ` を仮定し、Lemma 5.10 はさらに、どの f_a + 1 個の連続する view にも正直なリーダーがいることを仮定する。4 つの制約が同時に満たせることは Constraint/Witness の `constraints_satisfiable` が示す。

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
│       ├── Run.lean            署名の遡り（S にあれば署名者が前に送った）、腐敗の数え上げ、不変量の実行への持ち上げ
│       └── Witness.lean        Init・Honest・ByzBound・PartialSync を同時に満たす実行の例、輪番の lead が Fair を満たすこと
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

Algorithm 1 は 2 点で論文の擬似コードと違う。証明書が届いている限り同じスロットで view を進め続けること、そして view を進めてから提案と投票をし、転送をスロットの最後に回すこと。論文の擬似コードは各行を上から 1 回ずつ評価するだけなので、1 スロットに進める view は 16〜17 行の nullification で 1 つと続く 19〜21 行の M-notarisation で 1 つの高々 2 つで、view に入ったスロットでは提案できない。論文の証明はどちらの動作も前提にしていて、擬似コードのままでは付録の Lemma E.6（Timely view entry: 正直者が t に view v に入れば、全正直者は max(t, GST) から有界の遅れで v に入る）が成り立たない。

そのほかは、論文の記述を Lean に落とすための調整で、該当ファイルの冒頭の doc に「論文からの差異」として理由つきで書いてある。調整のうち、定理の読み方に関わるものは次の 4 つ。

| 差異 | 論文との関係 | 所在 |
|---|---|---|
| message はブロックの祖先を丸ごと運ぶ | 論文は祖先が届くことを Lemma 5.7・5.10 の証明で導く。通信モデルが論文より強い | Model/Transition/Basic |
| Lemma 5.8〜5.10 の δ は `PartialSync δ` として与える | GST 前に送った message にも GST + δ を課すので、論文の δ より強い仮定 | Analysis/Responsiveness/Lemma5_8 |
| log と finalise を形式化していない | Consistency と Liveness はブロックについての言明で、論文の log についての言明への還元は非形式的 | Analysis/Consistency/Lemma5_4 |
| `PartialSync` は Δ ≥ 1 を、Lemma 5.6・5.8・5.9 は v ≥ 1 を仮定に持つ | 論文の「t に送った message は t′ > t に届く」と、view の範囲 ℕ≥1 を明示したもの | Model/Constraint/Basic、各 Lemma |

## 未証明

- スロット内の動作の順序を固定している。tick と tick の間で原始関数がどの順に並んでも同じ状態に至ること、この固定順で表せない挙動が「送ったスロットの中で届く配送」だけであることは、形式化の外の議論に依っていて未証明。
