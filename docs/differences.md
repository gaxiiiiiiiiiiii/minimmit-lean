# 形式化の注記

## 1. 要約

論文 Minimmit（Chou, Lewis-Pye, O'Grady, [arXiv:2508.10862](https://arxiv.org/abs/2508.10862)）の §5 の Lemma 5.1〜5.10 を Lean 4 で機械検査した。対象は、§4 の Algorithm 1 を実行モデルの上で具体的に定義した形式化である。`sorry` はなく、依存公理は Lean の標準の 3 つで、CI がビルドと公理の監査を回す。

論文の証明に誤りは見つからなかった。ただし擬似コードを字義どおりに読むと証明の時間計算が通らない箇所があり、3 に述べるとおり評価順を証明が前提とする動作に合わせた。そのほか、4 に挙げるとおり、定義と定理の仮定・結論のいくつかを論文と違う形で定めた。論文の主張が成り立つのは、これらのうえでのことである。

log と finalise、§6 の最適化は対象外。

## 2. 対象と確かめ方

基準は論文の v7（2026-01-27）。対象は §4 の Algorithm 1 と §5 の 10 補題で、§2 のモデルはそのために必要な範囲で形式化した。

定理が論文のどの主張に当たるかは README の「状態」の表で、論文の概念がどの定義に当たるかは README の「論文との対応」で確かめられる。各定義と定理の意味は docstring に、依存公理は `Minimmit/Axioms.lean` にある。差異の理由の詳細は、各項目が挙げる定義や定理を置くファイルの冒頭 doc の「論文からの差異」にあり、ファイルは README で引ける。定理の仮定 `Init`・`Honest`・`ByzBound`・`PartialSync` が同時に満たせることは Model/Constraint/Witness の `constraints_satisfiable` で示してあり、定理は空虚に真ではない。

## 3. Algorithm 1 の実行方式

`Algo.step` は、評価順と、view を進める動作 `climb` の繰り返しの 2 点で論文の擬似コードと違う。

### 3.1 論文の記述

Algorithm 1 は「At every timeslot t:」の下に 2〜32 行を並べ、各スロットに上から 1 回評価する形で書かれている。一方、§3 の地の文は「Upon entering view v, p_i finds …」「proceeds to view v + 1 immediately upon seeing an M-notarisation」と、条件が成立した時点で処理すると述べている。§5 の証明は地の文に沿っていて、Lemma 5.6 の証明は「p_j が新しい証明書を転送するので全正直者は t + Δ までに view v に入る」「p_i はしたがって t + Δ までに新しいブロックを配る」と述べている。

### 3.2 問題

各行を 1 回ずつ順に評価すると、証明が使う動作が 2 つ起きない。まず提案と転送が遅れる。view に入るのは 16〜21 行で、提案の 5〜7 行より後にある。そのため view に入ったスロットには提案できず、そのスロットで完成した証明書も次のスロットの 2〜3 行まで転送されない。5.6・5.8・5.9 の証明の時間計算は、入った時点で提案し届いた時点で転送することを使うので、書いてあるとおりには通らず 1〜2 スロットずれる。ずれは定数で、O(·) の主張は変わらない。

次に、view の進み方が足りない。16〜17 行の nullification と 19〜21 行の M-notarisation で、1 スロットに進める view は高々 2 つである。GST 前に配送が遅れて証明書が一括で届く正直者は、遅れの分だけ多くのスロットを要する。「t + Δ までに全員が v に入る」は、v と遅れの差に応じて破れる。

### 3.3 対処

行の順を変え、16〜21 行を繰り返す。16〜21 行を現在の view の証明書がある限り繰り返し、次に 5〜14 行と 24〜28 行を評価し、2〜3 行の転送をスロットの最後に置く。これで、view に入ったスロットに提案し、そのスロットで完成した証明書を同じスロットで転送する。地の文の述べる動作と一致し、Commonware の実装仕様がリーダーは view に入った時点で提案し `enter_view` は現在より大きい view へ直接移ると定めていることとも合う。

§6.1 の「view を飛ばす」最適化は同じ穴を塞ぐもので、こちらは飛ばさず 1 view ずつ登る。§6.1 が追加する 2 つの規則は、順に登れば別の規則なしに満たされる。

## 4. 設計判断

論文の記述を Lean に落とすときに、論文と違う形を選んだもの。

### 4.1 定義

- 論文ではブロックの親をハッシュ値で参照している。`Block` は親ブロックそのものを持つ。ハッシュは衝突しないと仮定されているので、どちらの参照でも親は一意に定まる。違いは、ブロックを含む message を受け取れば祖先も手元にあることで、論文が Lemma 5.7 と 5.10 の証明で別に導く「祖先が届く」議論が要らない。5.10 の上界への影響は 4.3 に述べる。
- 論文ではブロック、票、nullify を出した処理系の署名付きとしている。`Block` と、`Msg` の票と nullify は署名者を成分に持つ。論文では署名を偽造不能と仮定しているので、署名を持つことと署名者を記すことは同じである。取引は環境が出すものと決まっているので署名者を記さない。
- 論文では Tr* から重複を除いている。`Block.trStar` は祖先の取引列を連結するだけで、重複を除去しない。Lemma 5.7 の結論は重複の有無に依らない。
- 論文ではスロット内の事象の順序を定めていない。`State.step` は、1 スロットの中で起きること、すなわち各プロセッサの動作、時刻の進行、配送、取引の投入、腐敗を、この順に適用する。順序の固定が挙動を狭めないことは未証明で、5 に述べる。
- 論文では Table 2 で初期の S に genesis の M/L-notarisation を含めている。本形式化では初期状態の S は空で、`MNotarised`・`LNotarised` が genesis を無条件に認める。S 上の述語の値は、初期 S に genesis の notarisation を含めた場合と同じである。
- 論文では「辞書順最小」や「some b」で 1 つを選んでいる。本形式化では S を `Finset.toList` で並べた順で先のものを取る。論文の証明は選択の仕方を使わないので、この選択はその一例である。
- 論文では、S に L-notarisation があるブロックを log に加える動作を finalise としている。`Processor` は log を持たず、`Algo.step` に finalise の動作はない。本形式化では、finalise したことを S に L-notarisation があることで表す。log の代わりに何について述べるかは 4.3 に述べる。

### 4.2 定理の仮定

- 論文では、t に送った message は max(GST, t) + Δ までに届くとしている。`State.Timely` は配送の期限をスロット境界で判定する。状態はスロットの冒頭にしかないので、そのスロットの冒頭で宛先の S にあることとして述べる。
- 論文では、t に送った message は t′ > t に届くとしていて、Δ ≥ 1 はそこから従う。`PartialSync` はこれを明示する。配送の期限をスロット境界で判定しているため、Δ = 0 では timer = 2Δ が二度と成り立たず Lemma 5.5 が偽になる。
- 論文では δ ≤ Δ を GST 後の実際の遅延の上界としている。本形式化では Lemma 5.8〜5.10 の δ を `PartialSync δ`、つまり「t に送った message は max(GST, t) + δ までに届く」として置く。Lewis-Pye と Roughgarden の Permissionless Consensus 7.5 節の δ の定義と同じ形である。timeout の 2Δ は `Honest` の Δ のままである。
- 論文では lead(v) = p_{(v mod n)+1} と固定している。本形式化では lead を任意の関数とし、論文の証明が輪番を使う 2 箇所を仮定に置く。Lemma 5.7 の `liveness` は `Fair`、つまりどのプロセッサもどの view 以降にもリーダーになることを、Lemma 5.10 の `optimistic_responsiveness` は、どの f_a + 1 個の連続する view にも正直なリーダーがいることを仮定する。5.10 の f_a はこの条件のパラメータで、定理は f_a ≤ f を課さない。論文の輪番は `Fair` を満たし、f_a 人以下の腐敗のもとで 5.10 の条件も満たすので、論文の設定を含む。この 2 つは `roundRobin_fair` と `roundRobin_correct_leader` で証明した。
- 論文では view を 1 以上としている。Lemma 5.6 の `correct_leader_finalises`、5.8 の `correct_leader_finalises_fast`、5.9 の `leave_view` は view v ≥ 1 を仮定に持つ。`View` は 0 を含み、v = 0 では誰も view 0 にいないので結論が成り立たない。
- 論文では正直者 p_i・p_j について述べている。Lemma 5.4 の `consistency` は p_i・p_j の正直さを、5.7 の `liveness` は p_j の正直さを仮定しない。署名の遡りは腐敗したプロセッサの S でも成り立ち、配送は腐敗したプロセッサ宛にも保証されるので要らず、論文の主張を含む。

### 4.3 定理の結論

- 論文では「every correct processor enters every view v」としている。Lemma 5.5 の `progression` は「view v 以上に達する」と述べる。3 の登り切りでは 1 スロットで v を通り過ぎることがあるが、view は 1 ずつ進むので通過はする。
- 論文では Lemma 5.8〜5.10 の上界を O(·) で述べている。`correct_leader_finalises_fast`、`leave_view`、`optimistic_responsiveness` は具体的な上界を持つ。5.8 の t + 3δ と 5.9 の t + 2Δ + 3δ は論文の証明本文の数字で、5.10 の t + δ + (f_a + 1)(2Δ + 3δ) + 3δ は、取引が全正直者に届く t + δ に、5.9 の上界を f_a + 1 view 分と 5.8 の上界を足したものである。具体的な上界は O(·) の主張を含む。
- 論文では Lemma 5.10 の証明の最後で「correct processors receive all ancestors of b by t + O(f_a Δ + δ)」を見積もっている。`optimistic_responsiveness` の上界に、祖先が届くまでの時間は含まない。4.1 のとおり message がブロックの祖先を丸ごと運ぶので、この分が要らない。
- 論文では Lemma 5.4・5.7・5.10 の結論を log で述べている。`consistency`・`liveness`・`optimistic_responsiveness` は、S に L-notarisation があるブロックについて述べる。論文の log_i(t) は、時刻 t に p_i の S が L-notarisation を持つブロックの Tr* に当たる。`consistency` は 2 つの log が整合することを、その 2 つのブロックの一方が他方の祖先であることで、`liveness` と `optimistic_responsiveness` は tr が log に入ることを、S に L-notarisation があるブロック b について tr ∈ Tr*(b) となることで述べる。

## 5. 未証明

スロット内の動作の順序を 4.1 のとおり固定していることについて、tick と tick の間で原始関数がどの順に並んでも同じ状態に至ること、この固定順で表せない挙動が「送ったスロットの中で届く配送」だけであることは、可換性による形式化の外の議論に依っていて未証明。

## 6. 参考

- 論文: Brendan Kobayashi Chou, Andrew Lewis-Pye, Patrick O'Grady, "Minimmit: Fast Finality with Even Faster Blocks", [arXiv:2508.10862](https://arxiv.org/abs/2508.10862)。基準は v7（2026-01-27）、CC BY 4.0。
- δ の定義: Andrew Lewis-Pye, Tim Roughgarden, "Permissionless Consensus", [arXiv:2304.14701](https://arxiv.org/abs/2304.14701)、7.5 節。
- 実装の仕様書: Commonware の [minimmit.md](https://github.com/commonwarexyz/monorepo/blob/4ff08da00068d61d50f745be2942d6a45597ed46/pipeline/minimmit/minimmit.md)（monorepo、2026-01-22 時点、Apache-2.0 と MIT）。論文の Algorithm 1 でなく実装の仕様で、「On 発火条件: 処理」の形で書かれている。
