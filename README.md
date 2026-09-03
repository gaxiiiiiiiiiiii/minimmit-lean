# minimmit-lean

BFT コンセンサスプロトコル Minimmit（Chou et al., [arXiv:2508.10862](https://arxiv.org/abs/2508.10862)）の Lean 4 による形式化。論文 §4 の Algorithm 1 を実行モデルの上で関数として定義し、§5 の Lemma 5.1〜5.10 を証明する。

学習のための自前の形式化で、[NyxFoundation/minimmit-fv](https://github.com/NyxFoundation/minimmit-fv) とは独立に作った。minimmit-fv はプロトコルの性質を仮定の構造体に切り出して補題を導くのに対し、ここでは状態遷移とアルゴリズムを具体的に定義し、補題はその実行について証明する。

## 状態

Lemma 5.1〜5.10 はすべて証明済み。`sorry` はなく、各定理が依存する公理は `propext`・`Classical.choice`・`Quot.sound` のみ。

| 論文 | 定理 | ファイル |
|---|---|---|
| Lemma 5.1 One vote per view | `one_vote_per_view` | Analysis/Consistency |
| Lemma 5.2 (X1) | `x1` | Analysis/Consistency |
| Lemma 5.3 (X2) | `x2` | Analysis/Consistency |
| Lemma 5.4 Consistency | `finalised_compatible`, `consistency` | Analysis/Consistency |
| Lemma 5.5 Progression through views | `progression` | Analysis/Liveness |
| Lemma 5.6 Correct leaders finalise blocks | `correct_leader_finalises` | Analysis/Liveness |
| Lemma 5.7 Liveness | `liveness` | Analysis/Liveness |
| Lemma 5.8 | `correct_leader_finalises_fast` | Analysis/Responsiveness |
| Lemma 5.9 | `leave_view` | Analysis/Responsiveness |
| Lemma 5.10 Optimistic responsiveness | `optimistic_responsiveness` | Analysis/Responsiveness |

## ビルド

Lean `v4.29.1`、Mathlib `v4.29.1`。

```
lake exe cache get
lake build
```

## モデルの読み方

時間は離散のスロット。各スロットで、各プロセッサが動作の列を起こし、次に網から message が届き、取引が投入され、腐敗が起きる。

- `Processor`: p_i の局所状態。Table 2 の view・T（`timer`）・nullified・proposed・notarised・S に、前スロットの動作を終えた時点の S である `prevS` を加えたもの。
- `State`: 大域状態。各プロセッサ `procs`、これまでに腐敗した `byz`、網に載った packet の全体 `pool`、現在のスロット `now`。
- `Action`: プロセッサが自分から起こす動作。message を送るか、次の view へ進むか。
- `Instr`: 1 スロット分の指示。各プロセッサの動作列・配送・取引投入・腐敗。敵対者は指示の列 `instrs : Nat → Instr` を選ぶ。
- `State.run s₀ instrs t`: スロット t の冒頭の状態。
- `Algo.step`: Algorithm 1。局所状態から 1 スロット分の動作列を返す関数。
- 制約: `Init`（初期状態）、`Honest`（腐敗していないプロセッサの動作は `Algo.step` の出力）、`ByzBound`（腐敗は f 人以下）、`PartialSync`（GST と Δ、Δ ≥ 1）、`Fair`（どのプロセッサも無限回リーダーになる）。
- 証明書は S 上の述語。`MNotarised`・`LNotarised`・`Nullified`・`ValidProposal`・`NoProgress`。
- finalise は動作を伴わない。S に L-notarisation があることで表す。

定理は「`Init s₀`、`Honest`、`ByzBound f`、`PartialSync Δ` を満たす任意の `s₀` と `instrs` について」の形で述べる。

## ファイル構成

```
Minimmit/
  Model/
    Transition.lean     状態、message、原始関数（send・progress・deliver・submit・corrupt）、State.step、State.run
    Certificate.lean    §4 の述語（M/L-notarisation、nullification、valid proposal、proof of no progress）
    Algo.lean           Algorithm 1（Algo.step）と部品（SelectParent、ProposeChild、転送、登り）
    Constraint.lean     Init、PartialSync、Correct、ByzBound、Fair、Honest
  Analysis/
    Transition.lean     原始関数の局所効果、動作列の畳み込み、1 スロット後の状態との関係
    Certificate.lean    述語の単調性、投票者・nullify 送信者の集合
    Run.lean            署名付き message の遡り（S にあれば署名者が前に送った）、腐敗の数え上げ
    Algo.lean           Algo.step の段ごとの分解、各段の送信条件、局所不変量（LocalInv・PropInv）、登りの補題
    Consistency.lean    局所不変量の実行への持ち上げ、Lemma 5.1〜5.4
    Timing.lean         view と timer の推移、部分同期による配送、証明書の転送、証明書への反応
    Liveness.lean       Lemma 5.5〜5.7 と、5.6 の補題群（LeaderRound）
    Responsiveness.lean Lemma 5.8〜5.10
```

## 論文からの差異

### Algorithm 1 の評価順と繰り返し

論文の Algorithm 1 は各スロットで 2〜32 行を上から 1 回評価する。ここでは次の順で評価する。

1. 16〜21 行（view の前進）。現在の view の証明書がある限り繰り返す。
2. 5〜7 行（提案）
3. 9〜11 行（投票）
4. 13〜14 行（timeout の nullify）
5. 24〜28 行（進捗のなさの nullify）
6. 2〜3 行（新しい証明書の転送）

順序を変えた理由は、論文の行順では view に入ったスロットで提案できず、そのスロットで完成した証明書を同じスロットで転送できないため。Lemma 5.6 以降の時間の議論は、入った時点で提案し届いた時点で転送することを前提にしており、行順のままでは 1〜2 スロットずれる。

繰り返しにした理由は、Lemma 5.6 の証明と付録の Lemma E.6 が「最初の正直者が t に view v に入れば、全正直者は t + Δ までに v に入る」と主張していて、これが 1 回評価では成り立たないため。1 回評価では 1 スロットに高々 2 view しか進めない。GST 前に配送が遅れていた正直者は、GST + Δ に複数の view の証明書を一括で受け取っても 1 スロットに 1〜2 view ずつしか登れず、リーダーがその状態にあると 5.6〜5.10 の結論が偽になる実行がある。証明書がある限り登り切る動作なら、t + Δ までに全員が v に入り、論文の議論がそのまま通る。§6.1 の「view を飛ばす」最適化とは別で、ここでは順に 1 view ずつ登る。

### 転送

2〜3 行の転送は、新しい証明書を構成する message を S にある分すべて送る。論文は辞書順で最小の 2f + 1 個を 1 組選ぶ。L-notarisation は論文の脚注 12 のとおり転送しない。「新しい」は、動作を終えた時点の S にあって前スロットの動作を終えた時点の S になかったこと。

### モデル

- Δ ≥ 1 を `PartialSync` に明示する。論文の「t に送った message は t′ > t に届く」から従う条件で、Δ = 0 では timer = 2Δ が二度と成り立たず Lemma 5.5 が偽になる。
- 配送の期限はスロット境界で判定する。
- Tr* は祖先の payload を連結するだけで、重複を除去しない。

### ステートメント

- Lemma 5.6・5.8・5.9 は view v ≥ 1 を仮定に持つ。論文の view は ℕ≥1 で、v = 0 では誰も view 0 にいないので結論が成り立たない。
- Lemma 5.8〜5.10 の O(·) は具体的な上界に置き換えた。5.8 は t + 3δ、5.9 は t + 2Δ + 3δ、5.10 は t + δ + (f_a + 1)(2Δ + 3δ) + 3δ。
- Lemma 5.10 のリーダーの条件は「どの f_a + 1 個の連続する view にも正直なリーダーがいる」。論文の輪番 lead(v) = p_{(v mod n)+1} は f_a 人以下の腐敗のもとでこれを満たす。
- Lemma 5.8〜5.10 の δ は `PartialSync δ` として与える。timeout の 2Δ は Honest の Δ のまま。

## 未証明

- スロット内の動作の順序を固定している。tick と tick の間で原始関数がどの順に並んでも同じ状態に至ること、この固定順で表せない挙動が「送ったスロットの中で届く配送」だけであることは、形式化の外の議論に依っていて未証明。
