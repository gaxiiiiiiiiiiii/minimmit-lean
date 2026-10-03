# minimmit-lean

BFT コンセンサスプロトコル Minimmit（Chou et al., [arXiv:2508.10862](https://arxiv.org/abs/2508.10862)）の Lean 4 による形式化。論文 §4 の Algorithm 1 を実行モデルの上で関数として定義し、§5 の Lemma 5.1〜5.10 を証明する。

学習のための自前の形式化で、[NyxFoundation/minimmit-fv](https://github.com/NyxFoundation/minimmit-fv) とは独立に作った。minimmit-fv はプロトコルの性質を仮定の構造体に切り出して補題を導くのに対し、ここでは状態遷移とアルゴリズムを具体的に定義し、補題はその実行について証明する。

## 状態

Lemma 5.1〜5.10 はすべて証明済み。`sorry` はなく、各定理が依存する公理は `propext`・`Classical.choice`・`Quot.sound` のみ。`Minimmit/Axioms.lean` が主定理ごとにこれを `#guard_msgs` で固定し、GitHub Actions の CI が push ごとにビルドと、ライブラリ全体の公理の監査を回す。

論文の記述との対応と、論文と違う形にした点は [CORRESPONDENCE.md](CORRESPONDENCE.md) にまとめてある。

## ビルド

Lean `v4.29.1`、Mathlib `v4.29.1`。

```
lake exe cache get
lake build
```

定理はすべて名前空間 `Minimmit` にある。依存公理は次で確認できる。

```
printf 'import Minimmit\n#print axioms Minimmit.tx_finalised\n' | lake env lean --stdin
```

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
│       ├── Basic.lean          Init、PartialSync、Correct、ByzBound、Fair、Honest、IsMinimmit
│       ├── Run.lean            署名の遡り（S にあれば署名者が前に送った）、腐敗の数え上げ、不変量の実行への持ち上げ
│       └── Witness.lean        IsMinimmit を満たす実行の例、輪番の lead が Fair と 5.10 のリーダーの仮定を満たすこと
└── Analysis
    ├── Log.lean                log と、§2 の compatible・Consistency・Liveness の定義
    ├── Latency.lean            §5.3 の optimistic responsiveness の定義
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
