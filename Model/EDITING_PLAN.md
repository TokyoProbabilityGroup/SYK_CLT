# 共有 SYK 模型の編集計画

## 管理範囲と現状

実行する単位とその状態は [全体計画](../EDITING_PLAN.md) で管理する。この文書は Model 内のファイル群について、完了した W01–W04 の現況と、W06・F04・Z01 の担当範囲を記録する。完了済み作業の詳しい検証記録は [作業履歴](../WORK_HISTORY.md) の該当節を参照する。W06・F04 で共有補題を追加する場合は、担当範囲をそれぞれの詳細計画で確定し、Model の規則と検証条件も適用する。利用側や Blueprint の編集細目は、その担当ディレクトリの計画書に置く。作業単位内のチェック項目は、個別の承認やコミットの区切りではない。

2026-09-08、コミット `05d64f4` の配置・宣言を基に文書を再編した。以下の表はその後の完了記録を反映した現状であり、検証根拠は各単位の記録を参照する。

| 内容 | 現状と残作業 |
| --- | --- |
| パラメータ・共有代数 | 逆温度の分離、相互作用添字、昇順積、位相、相互作用演算子、確定的ハミルトニアンは移行済み |
| 有限次元の解析・物理量 | 通常の分配関数、`normalizedTrace`、物理的 Gibbs API、実方向微分、整関数性・複素微分・条件付き対数微分は実装・検証済み。零点のない領域は Z01 |
| ガウス型相互作用 | `CouplingSpace`・`couplingSpace_card`・`standardGaussianMeasure` は Model に移設済み。汎用測度との接続は W02、標準スケールとハミルトニアンは W03 で共有化 |
| 標準表現 | W04 で Jordan–Wigner 表現と同じ偶数次数の相互作用の直交性を構成・検証済み。抽象的な `MajoranaSystem` の仮定は追加していない |
| 利用側 | 集中不等式の移行は W05 で完了。CLT の有限模型・モーメント・対数と標準表現の規格化の照合は W06 で完了。後続の補助モジュールの接続は [CLT の統合監査](../CLT/EDITING_PLAN.md#integration-audit-2026-09-26) を参照 |

<a id="w01"></a>

## W01：共有行列解析の仕上げ

`FiniteDimensionalGibbs.lean` の整関数性・複素微分・非零性を仮定した対数微分は検証済み。零点のない領域の証明は Z01 で扱う。[検証記録](../WORK_HISTORY.md#model-w01)を参照する。

<a id="w02"></a>

## W02：汎用ガウス測度への接続

`GaussianDisorder.lean` は独立した汎用標準ガウス測度を利用する。利用側の移行は [SuperConcentration の W02](../SuperConcentration/EDITING_PLAN.md#w02) に従う。[検証記録](../WORK_HISTORY.md#model-w02)を参照する。

<a id="w03"></a>

## W03：ガウス型 SYK ハミルトニアンの共有化

標準スケールと標準規格化ハミルトニアンは `GaussianDisorder.lean` に共有済み。係数の分散は `(q-1)! / N^(q-1)`。[検証記録](../WORK_HISTORY.md#model-w03)を参照する。

<a id="w04"></a>

## W04：標準行列表現の構成

Jordan–Wigner 表現、次元 `2^(N/2)`、同じ偶数次数の相互作用族の規格化トレース直交性は検証済み。[検証記録](../WORK_HISTORY.md#model-w04)を参照する。

## 利用側への接続

- W02 の汎用証明は [Probability/GaussianConcentration の計画](../Probability/GaussianConcentration/EDITING_PLAN.md)、旧配置・利用側の移行と W05 は [SuperConcentration の計画](../SuperConcentration/EDITING_PLAN.md) が管理する。
- CLT 固有の規格化分配関数、`Z(0)=1`、通常トレースとの対応は一般の非空有限次元表現について実装済みである。[W06](../CLT/EDITING_PLAN.md#w06) では標準表現と原稿の規格化との対応を照合し、モーメント・トレース零・`Z≥1` などの有限模型の証明を完了した。集中評価の移送は必須前提にしない。
- `Annealed_FE` は過去の共有 API 移行では編集対象外だった。旧 API による当時の破損は履歴であり、現行検査では再現していない。既定対象からの除外は同ライブラリの個別検証を意味せず、CLT が直接読み込む依存先としての影響を確認する。
- Blueprint の編集細目は [Chapters の計画](../Chapters/EDITING_PLAN.md) が管理する。全体計画に従い、対応する実装単位内で完了する。

<a id="f04-model"></a>

## W06・F04：Model 内の共有補題

W06 の追加証明は実際には `CLT/Main.lean` に実装され、Model の既存 API を利用して完了した。トレース零・有限行列の下界・成長評価が Model に追加済みだとは扱わない。後続で共有が必要になった補題は `Majorana.lean`・`GaussianDisorder.lean`・`FiniteDimensionalGibbs.lean` の適切な層へ移し、CLT 固有の規格化や漸近は Model に移さない。検証根拠は [CLT の W06](../CLT/EDITING_PLAN.md#w06) に従う。

F04 で行列解析を共有する場合は、[CLT の形式化計画](../CLT/EDITING_PLAN.md#formalization)で対象の定理文と利用先を確定してから既存ファイルへ追加する。F01 のガウス–エルミート部分積分を `Z_N` に適用するため、必要な階数の正則性・偏導関数の指数増大評価も供給する。汎用ガウス部分積分は Model に置かない。各変更ファイルの個別検査と `lake build Model SuperConcentration CLT` を行い、主要定理の仮定と公理依存を確認する。両単位の状態は全体計画で管理する。

後続の F04-M では、`CLT/Lemmas/SingularValues.lean` と `CLT/Lemmas/MatrixTraceExponential.lean` の汎用行列結果と既存の Model の規格化トレース・分配関数の型と利用先を比較する。スカラー型や規格化が異なる宣言を機械的に統一しない。共有する結果が確定した場合にだけ Model の適切な既存ファイルへ置く。作業票の詳細は [F04-M](../CLT/EDITING_PLAN.md#ticket-f04-m) に置く。

<a id="z01"></a>

## Z01：零点のない領域

これは W01–W06 と別の後続課題であり、必要な領域・一様性の選定前には実装へ進まない。CLT 側は要件をここへ集約し、同じ進捗チェックを持たない。

- [ ] CLT が必要とする円板・帯状領域と、一様性の対象（`N`・ハミルトニアン・逆温度）を精査する。
- [ ] 固定したハミルトニアンに対する実軸近傍など、最初に証明する具体的な領域を選定する。
- [ ] 一様な非零性を内部で証明するか、正確な外部結果を入力とするかを決め、必要な承認を得る。
- [ ] 非零性の定理から条件付き API の `Z z ≠ 0` を供給する。
- [ ] 正則な対数が必要な場合に限り、単連結性など枝を選ぶ条件を明示して構成する。

全複素平面での非零性や複素逆温度における正値性は目標にしない。完了条件は、選定した領域で必要な仮定を供給でき、外部入力と内部で証明した結果が区別されていることとする。

## 各単位の検証と記録

変更ファイルを個別に `lake env lean` で検査し、`lake build Model` と移行済み利用側の最小ビルドを行う。Model と集中不等式の接続を変更した単位では `lake build Model SuperConcentration` を実行する。重要な定理では `#print axioms` と定理文の仮定を確認する。

ワークスペース全体に影響する変更では `lake build` を実行する。Blueprint の変更では本文と宣言参照を照合し、Verso 復帰後に `lake lean SYK/BlueprintMain.lean -- --run SYK/BlueprintMain.lean --output SYK/_out/site` と `lake exe vbp check --site SYK/_out/site` を実行する。現在の既定ビルドから除外されている `Annealed_FE` と `Universality` は個別に検証済みとは扱わない。既定範囲には新規の `sorry`、`admit`、`axiom`、未解決の証明目標を許容しない。

検証時は対象コミット・差分、コマンド、結果、警告、公理依存、残る仮定を記録する。該当単位の節には現行の結論と残作業を反映し、詳しい完了記録は [作業履歴](../WORK_HISTORY.md) の対応する節へ移す。過去の成功を変更後の成功として転記しない。

旧段階0–2の実装・検証記録は [作業履歴](../WORK_HISTORY.md#model-legacy) に保存した。
