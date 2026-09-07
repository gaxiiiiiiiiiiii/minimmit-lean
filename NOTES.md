# 形式化の注記

## 1. 要約

論文 Minimmit（Chou, Lewis-Pye, O'Grady, [arXiv:2508.10862](https://arxiv.org/abs/2508.10862)）の §5 の Lemma 5.1〜5.10 を Lean 4 で機械検査した。対象は、§4 の Algorithm 1 を実行モデルの上で具体的に定義した形式化である。§2 の Consistency と Liveness は、その定義どおりの文で証明した。`sorry` はなく、依存公理は Lean の標準の 3 つで、CI がビルドと公理の監査を回す。

論文の証明に誤りは見つからなかった。ただし論文の主張が成り立つのは、Algorithm 1 の評価順を変え（3）、いくつかを論文と違う形にした（4）うえでのことである。疑似コードを字義どおりに読むと、証明の時間計算が通らない箇所がある（3）。

§6 の最適化は対象外。

## 2. 対象と確かめ方

基準は論文の v7（2026-01-27）。対象は §4 の Algorithm 1 と §5 の 10 補題で、§2 のモデルはそのために必要な範囲で形式化した。

定理が論文のどの主張に当たるかは README の「状態」の表で、論文の概念がどの定義に当たるかは README の「論文との対応」で確かめられる。各定義と定理の意味は docstring に、依存公理は `Minimmit/Axioms.lean` にある。定理の仮定 `Init`・`Honest`・`ByzBound`・`PartialSync` が同時に満たせることは Model/Constraint/Witness の `constraints_satisfiable` で示してあり、定理は空虚に真ではない。

## 3. Algorithm 1 の実行方式

論文の疑似コードは逐次実行を想定した書き方だが、証明はイベント駆動的な挙動、すなわち、条件を満たせばその都度処理が実行されると想定しているかのように書かれている。疑似コードが、実際の実行順や繰り返し処理を想定して書かれていないため、字義通り実行すると証明の求める挙動とならない。意図通りとなるようにアルゴリズムを調整した。

調整は 2 点である。view の前進を証明書がある限り繰り返す繰り返し処理を先頭に、新しい証明書を全員へ送る処理を最後尾に、それぞれ配置した。

## 4. 設計判断

論文の記述を Lean に落とすときに、論文と違う形を選んだもの。

### 4.1 定義

- 論文ではブロックの親をハッシュ値で参照している。本形式化では親ブロックそのものを持つ。ハッシュは衝突しないと仮定されているので、どちらの参照でも親は一意に定まる。S がブロックを含むかどうかは `containsBlock` で別に判定し、親には及ばない。
- 論文では、ブロック、票、nullify は出した処理系の署名付きである。本形式化では、ブロック、票、nullify が署名者を成分に持ち、取引は環境が出すものと決まっているので署名者を記さない。論文では署名を偽造不能と仮定しているので、署名を持つことと署名者を記すことは同じである。
- 論文ではスロット内の事象の順序を定めていない。本形式化では、1 スロットの中で起きること、すなわち各プロセッサの動作、時刻の進行、配送、取引の投入、腐敗を、この順に適用する。順序の固定が挙動を狭めないことは未証明である（5 を見よ）。
- 本形式化では、「辞書順最小」や「some b」の選択を S の列挙順とする。論文の証明は選択の仕方を使わない。
- 論文では log は finalise が書く変数である。本形式化では log は S から定まる関数 `log` で、finalise したブロックのうち最も深いものの Tr* をとる。finalise したことは `Finalised`、つまり S に L-notarisation があり全祖先を含むことで表す。

### 4.2 定理の仮定

- `PartialSync` に Δ ≥ 1 を明示した。§2 の「t に送った message は t′ > t に届く」から従う条件だが、配送の期限をスロット境界で判定しているため、Δ = 0 では timer = 2Δ が二度と成り立たず Lemma 5.5 が偽になる。
- Lemma 5.8〜5.10 の δ は、Lewis-Pye と Roughgarden の Permissionless Consensus 7.5 節の定義に合わせ、「t に送った message は max(GST, t) + δ までに届く」として置いた（`PartialSync δ`）。
- 論文では lead を輪番に固定している。本形式化では lead に実装を与えず、満たすべき条件 `Fair` と `CorrectLeaderWithin` に抽象化した。輪番がどちらも満たすことは `roundRobin_fair` と `roundRobin_correct_leader` で証明してある。

### 4.3 定理の結論

- Lemma 5.8〜5.10 の O(·) は具体的な上界に置き換えた。5.8 の t + 3δ と 5.9 の t + 2Δ + 3δ は論文の証明本文の数字で、5.10 の t + δ + (f_a + 1)(2Δ + 3δ) + 3δ は 5.9 を f_a + 1 view 分と 5.8 の和である。

## 5. 未証明

スロット内の動作の順序を固定していること（4.1）について、tick と tick の間で原始関数がどの順に並んでも同じ状態に至ること、この固定順で表せない挙動が「送ったスロットの中で届く配送」だけであることは、可換性による形式化の外の議論に依っていて未証明。

## 6. 参考

- 論文: Brendan Kobayashi Chou, Andrew Lewis-Pye, Patrick O'Grady, "Minimmit: Fast Finality with Even Faster Blocks", [arXiv:2508.10862](https://arxiv.org/abs/2508.10862)。基準は v7（2026-01-27）、CC BY 4.0。
- δ の定義: Andrew Lewis-Pye, Tim Roughgarden, "Permissionless Consensus", [arXiv:2304.14701](https://arxiv.org/abs/2304.14701)、7.5 節。
- 実装の仕様書: Commonware の [minimmit.md](https://github.com/commonwarexyz/monorepo/blob/4ff08da00068d61d50f745be2942d6a45597ed46/pipeline/minimmit/minimmit.md)（monorepo、2026-01-22 時点、Apache-2.0 と MIT）。論文の Algorithm 1 でなく実装の仕様で、「On 発火条件: 処理」の形で書かれている。
