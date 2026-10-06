# SYK 中心極限定理の編集計画

## 現在の範囲

現在の条件付き CLT は実装済みであり、`AnnealedInput` は現行原稿の `prop:annealed-free-energy` の命題文に対応する内容を仮定として受け取る。対数の期待誤差の明示的評価と標準模型族への条件付き適用も実装・検証済みである。`CLT-REFACTOR` は現行実装を対象とする整理と監査・統合を完了した。命題自体の証明と、そのための外部入力の調査・凸関数列の補題の補完は「その他の残件」とする。原稿との対応と証明状態は [構造文書](ARCHITECTURE.md)、入力整理の検証は [作業履歴](../WORK_HISTORY.md#clt-input-2026-10-04) を参照する。

## 現在の検証状況

`CLT-LOG`・`CLT-APPLY` は完了した。Lean 4.32.2 で変更した2ファイルと直接の利用先 `Main.lean` の個別検査、`lake build CLT`、定理文・公理依存の確認を行った。参照原稿、開始時の差分、修正内容、警告と検証結果は [完了記録](../WORK_HISTORY.md#clt-log-apply-completion-2026-10-05) に集約する。`hFE : AnnealedInput` は明示的な仮定として残る。Verso の機械的検査は休止中である。

`CLT-REFACTOR` の第1巡は、新規2ファイルと変更・直接利用側を含む13ファイルの個別 Lean 検査、`lake build CLT`、移設12公開宣言の型・定義の比較、24主要宣言の公理依存確認を終えた。使用量の限度による停止から Kamijima を担当・統合担当として再開し、第1巡監査を終えて統合した。必須修正・任意提案・未解決事項はすべて0件で、追加の数学的変更・Lean 検証・監査巡回は行っていない。警告・原稿対応・残る仮定は [第1巡の記録](../WORK_HISTORY.md#clt-refactor-2026-10-06) を参照する。

## 完了した実装の仕様

作業の ID・状態・担当・依存関係は [全体計画](../EDITING_PLAN.md#残る作業) に集約する。以下は完了した LOG・APPLY の仕様と検証範囲である。

### 対数の期待誤差の明示的評価

対象は完了した `CLT-LOG`。実装は `Setting.cubed_scale_Y_lt_half_bounded` と `Setting.integral_log_Y_isBigO` にある。承認された編集範囲は `Lemmas/LogTaylor.lean`、`Lemmas/LogEventBound.lean`、`Lemmas/LogAsymptotics.lean`。統合済みの入力を使い、上流の定義や仮定を変更しない。

割当時の参照原稿・Lean ソース一式は [割当記録](../WORK_HISTORY.md#clt-log-apply-plan-2026-10-05) に記録した。入力は `S : Setting q` と `hFE : AnnealedInput q S`。`Setting.integral_logLinearError_le_variance_tail`、`Setting.scaled_varianceY_tendsto` と既存の小確率事象の評価を接続した。統合担当は実装後にこの計画・構造文書・全体計画・作業履歴と `Chapters/CLT.lean` を更新した。

`a=q/2-1`、`Y_N=Z_N/E Z_N` とし、原稿の非零の小さい実逆温度で `E[log Y_N]=O(N^(-2a))` を明示的な Lean 定理にした。`N^a` を掛けた期待誤差が零に収束することは実装済みであり、この評価の追加は条件付き CLT 自体の未完成証明を埋める作業ではない。

`LogTaylor.lean`・`LogEventBound.lean`・`LogAsymptotics.lean` の二次モーメント、小確率事象、`Z_N≥1` と `log E Z_N=O(N)` を再利用する。分布収束だけからモーメント評価を推論しない。完了条件は、原稿の評価と同じ指数・中心化・温度条件を照合し、個別検査・関連ビルド・公理依存確認を終えることである。

### 命題を仮定した具体模型への適用

対象は完了した `CLT-APPLY`。2026-10-05 に以下の仕様を確定し、実装・検証した。割当時の参照原稿・Lean ソース一式は [割当記録](../WORK_HISTORY.md#clt-log-apply-plan-2026-10-05) を参照する。

#### 標準模型族と編集範囲

新規 `StandardModel.lean` に標準模型族の構成、有限サイズの規格化との接続、条件付き CLT の具体的適用をまとめた。`SYK.CLT.Main` と `SYK.CLT.Normalization` を import する利用側とし、抽象的な `Main.lean` や共有 Model から逆向きに import していない。以下の模型族と原稿への対応を実装した。

公開した模型族の型は `standardSetting (q : ℕ) (hq : Even q) (hq4 : 4 ≤ q) : Setting q` である。`N n = q + 2 * n`、`d n = SYK.StandardBasis ((q + 2 * n) / 2)`、`majorana n = SYK.standardMajoranaSystem (q + 2 * n) ...` とし、有限性・非空性・偶数性・`q ≤ N n`・`Tendsto N atTop atTop` を既存定義と自然数の算術から構成した。`Setting` に仮定を追加していない。

任意の偶数 `N ≥ q` が一意に `q + 2 * n` と書けることを補題にし、原稿の偶数サイズ全体の極限との対応を示した。尺度は添字 `n` のべきに置き換えず、常に `(q + 2 * n)^(q/2-1)` とする。`partitionFunction_standard` から、この族の `Z` が `2^(-N/2) Tr(exp(-β H_N))` の実数値であることを示した。標準ガウス座標、係数分散 `(q-1)!/N^(q-1)`、位相 `i^(q/2)` と指数の負号を維持した。

数学ライブラリの編集範囲は新規 `CLT/StandardModel.lean` のみとした。既存 `Basic.lean`・`Main.lean`・`Normalization.lean`、LOG の3ファイル、共有模型・ビルド設定は変更を必要としなかった。統合担当は実装後に `CLT/ARCHITECTURE.md`、本計画、全体計画、作業履歴、`Chapters/CLT.lean` の対応を更新した。

#### 公開定理の仕様

名前空間は `SYK.CLT`。各定理は `{q : ℕ} (hq : Even q) (hq4 : 4 ≤ q)` と `hFE : AnnealedInput q (standardSetting q hq hq4)` を入力とする。`hq`・`hq4` は模型族を構成するために一度渡し、構成後の抽象 CLT 適用時には追加しない。以下の結論は `S := standardSetting q hq hq4` とした既存定理の結論を正確に使う。

| 新規公開定理 | 適用する既存定理と結論 |
| --- | --- |
| `standard_partition_and_log_partition_clt` | `partition_and_log_partition_clt S hFE`。一つの `∃ βq > 0` の下で、すべての実数 `β`、`abs β < βq`、`β ≠ 0` に対し、アニール圧力の収束、相対 CLT、中心化した対数 CLT、極限分散の正値性、全 `n` の `S.varianceZ β n > 0`、標準化 CLT を同時に結論する。 |
| `standard_partition_clt` | `partition_clt` の結論を上の共同定理から射影する。アニール圧力、相対 CLT、極限・有限サイズ分散の正値性、標準化 CLT を含む。 |
| `standard_log_partition_clt` | `log_partition_clt` の結論を上の共同定理から射影する。アニール圧力と中心化した対数 CLT を含む。 |

共同定理で同一の高温半径を供給し、個別定理はその証人を利用する。相対・対数 CLT の極限測度は `gaussianReal 0 (limitVariance q hFE.ℓ β)`、標準化 CLT は `gaussianReal 0 1`、極限確率変数は `fun x : ℝ ↦ x` とする。サイズごとの確率測度は `standardGaussianMeasure (q + 2 * n) q`。収束は `n → atTop` の `TendstoInDistribution` とし、共通確率空間や概収束を仮定しない。

`limitVariance` は `(q!/2) β² (deriv hFE.ℓ β)²`、相対変動は `N^(q/2-1) (Z/E Z-1)`、対数変動は `N^(q/2-1) (log Z-E log Z)`、標準化は `(Z-E Z)/sqrt(Var Z)` である。原稿の `subsec:SYK-model`、`eq:Y_N`、`eq:scaled-relative-clt`、`eq:standardized-clt`、`thm:partition-clt`、`thm:free-energy-clt` と照合する。

`hFE` はこの標準模型族に対する `prop:annealed-free-energy` の命題文の内容を仮定する。入力の構築、命題の証明、他の表現との表現独立性、任意のサイズ部分列への新しい API、LOG の明示的評価は本単位に含めない。一般表現への外部定理の適用を仮定せず、標準表現自体を対象にする。

#### 完了条件と検証

模型族の全フィールド、偶数サイズ全体との対応、規格化の橋渡し、上記3定理を実装し、原稿との対応と残る `hFE` を文書・Blueprint に反映した。具体模型族の構成と適用も検査した。

共有ワークスペースのルートで新規モジュールの依存をビルドしたうえで `lake env lean SYK/CLT/StandardModel.lean` と `lake build CLT` を実行した。`lake build CLT` には新規 `SYK.CLT.StandardModel` のビルドが含まれる。`#print` で3定理の型・仮定・尺度・分散を照合し、`#print axioms` で3定理と模型族・対応補題に `sorryAx` や新規公理がないことを確認した。Blueprint の本文・宣言参照はソース上で照合した。Verso の機械的検査は休止中である。検証結果の詳細は [完了記録](../WORK_HISTORY.md#clt-log-apply-completion-2026-10-05) を参照する。

## その他の残件

次の課題は現時点の `CLT-APPLY` や条件付き CLT の完了条件に含めない。再開する場合は全体計画の作業表に戻し、先行成果・数学的仕様・編集範囲・検証条件を確定する。

### 凸関数列の収束補題の補完

対象は保留中の `CLT-CONVEX`。再開時の編集候補は `Lemmas/ConvexDerivatives.lean`。既存の公開定理の型を保持し、不足部分を追加する。個別 Lean 検査と `lake build CLT` も完了条件に含める。

現行の `lem:convex-derivatives` は、全実軸上の微分可能な凸関数列の各点収束と `C¹` 極限から、関数・導関数の局所一様収束を結論する。既存の `convex_convergence_deriv_tendstoUniformlyOn` は関数の局所一様収束を仮定しており、補題全体の形式化ではない。

既存の導関数収束定理を再利用し、各点収束から関数の局所一様収束を導く部分を補い、原稿の全実軸での主張を証明する。原稿の証明省略を理由に外部仮定へ置き換えない。既存の開集合上の定理を維持してよく、不要な一般化は行わない。完了条件は正確な原稿の仮定から両方の局所一様収束を Lean が受理し、主要定理の公理依存を確認することである。

### 外部入力と構築仕様の調査

対象は保留中の `CLT-EXTERNAL`。再開時は固定した原稿、引用元、`Normalization.lean` と既存の入力宣言を読み取り調査する。引用元の版・定理文・規格化・温度範囲・収束・正則性と各フィールドの導出を照合し、残す外部仮定、内部で証明する補題、不足事項、後続の定理文・編集範囲・検証案を報告する。新しい仮定の採用や実装は行わない。

統合担当が調査結果を構造文書と後続仕様に反映する。新たな外部仮定の採否を研究者が判断し、公開定理の仮定と結論、編集ファイルを確定するまで、命題の証明に着手しない。

### `prop:annealed-free-energy` の証明

対象は保留中の `CLT-ANNEALED`。構築定理の正確な型と編集範囲は外部入力の調査後に確定する。現段階の説明だけから API や新規ファイルを作らない。

`Main.lean` の条件付き CLT は、一つの `S : Setting q` と `hFE : AnnealedInput q S` を入力として受け取る。`prop:annealed-free-energy` の内容をこの仮定として扱い、命題自体の Lean 証明は保留する。再開する場合は、現行の命題文を対象とし、He2026 から受け取る結果と原稿内で導く結果を分離する。対象模型、規格化、逆温度の範囲、正則性、収束の種類を確定してから、明示した外部入力から各フィールドを導く。

He2026 の定理自体の全面的な Lean 形式化は現在の計画に含めない。外部結果は名前を付けた明示的な仮定として受け取り、未検証の公理を導入しない。外部入力そのもの、そこからの導出、`AnnealedInput` を用いた条件付き CLT を別々に記録する。必要な導出が得られない場合は、数学的障害と追加判断・再開条件を報告する。完了条件は、確定した外部仮定から入力を構築し、公理依存とは別に残る仮定を確認することである。

`Annealed_FE/refs/SYK-HT-arxiv.tex` は別の Rademacher 模型の原稿であり、そこでの結果をこの入力の構築と同一視しない。`Annealed_FE` は現在の `CLT/Main.lean` の import 先ではない。

## 数学的実装後のリファクタリング

対象は `CLT-REFACTOR`。2026-10-06 の依頼により、現在の数学的実装を対象に範囲を確定した。担当・統合担当は Kamijima。作業・監査は最大3巡とする。保留中の `CLT-CONVEX`・`CLT-EXTERNAL`・`CLT-ANNEALED` は再開しない。開始点と参照原稿は [第1巡の記録](../WORK_HISTORY.md#clt-refactor-2026-10-06) に記す。

### 調査から確定した編集範囲

| 対象宣言・ファイル | 移設先・利用側 | 数学的役割と前後の依存 | 検証対象 |
| --- | --- | --- | --- |
| `CliffordSignParity` の `SYK.hermiteMulti`、`gaussianCouplings`、`hermite_aeval_neg`、`hermite_aeval_sign`、`integral_gaussianCouplings_sign`・`_perm`・`_signed_perm` | 新規 `Lemmas/GaussianHermiteBasic.lean`。`GaussianChaos` と `CliffordSignParity` が直接利用。模型の `IsEvenMultiIndex` を使う `Rademacher` は `CliffordSignParity` を明示 import | 任意の有限型上の Hermite 積と独立標準ガウスの対称性を、マヨラナ系の符号ゲージ・頂点偶奇則から分離する。従来の `GaussianChaos → CliffordSignParity → Model` を `GaussianChaos → GaussianHermiteBasic ← CliffordSignParity` に変え、汎用 Hermite 展開の模型依存を除く | 新規モジュール、両直接利用側、`GaussianHermiteOrthogonality`、`Preliminaries`、`Rademacher`、`HigherChaosProjection` |
| `GaussianQuadraticCLT` の `centeredGaussianSquare`、平均・二次モーメント、`normalizedQuadraticSum`、`normalizedQuadraticSum_law` とその局所補助 | 新規 `Lemmas/GaussianQuadraticObservable.lean`。`GaussianQuadraticCLT` と `GaussianFourthMoment` が直接利用。`IndependentFourthMoment` は `Setting` のため `Basic` を明示 import | 有限サイズのガウス二乗観測量と法則の移送を漸近 CLT から分離する。`GaussianFourthMoment → GaussianQuadraticCLT → SecondChaosAsymptotic` を、両者から観測量モジュールへの依存に変える。四次モーメントと独立和の評価が CLT を前提としなくなる | 新規モジュール、両直接利用側、`IndependentFourthMoment`、`QuadraticBridge`、`LogEventBound` |
| `SingularValues`・`MatrixTraceExponential`・`TraceExpDerivatives` | 現行配置を維持 | 外部の実利用先は `PartitionDerivatives` だけであり、共有 Model はこの層を利用していない。将来の利用のためだけにこの基盤を移さない | 関連 CLT ビルドと主要微分評価の型・公理依存 |
| `SYK.normalizedTrace` と `MatrixAnalysis.Matrix.normalizedTrace` | 現行配置を維持 | 前者は `ℂ`・非空型・`trace/card`、後者は一般の `RCLike`・空型可・`card⁻¹*trace`。規格化は利用側で照合済みであり、型と公開定義を保持した再編で統合しない | `PartitionDerivatives` の規格化接続と原稿 `eq:Z-derivative-bound` を照合 |

新規2ファイルは既存 `CLT` のグロブに含まれる。宣言名・名前空間・型・仮定・属性・規格化と証明の数学的内容を保持し、旧パスの互換モジュール・別名は作らない。共有ガウス基盤への移設は、同じ内容の部分積分 API が既にあり、今回の記法を使う実際の利用側が CLT 内に限られるため採用しない。共有基盤から CLT への import は作らない。

変更ファイル・直接利用側を依存順に `lake env lean` で検査し、必要な `olean` を生成して `lake build CLT` を実行する。主要移設宣言、微分評価、抽象・標準模型の CLT の型と公理依存を再確認する。構造文書・案内・全体計画・作業履歴と Blueprint の依存説明を更新する。章はソースだけを照合し、Verso の検査・生成は行わない。

実際の利用先と import を基に、重複定義、過剰な依存、不要な変換、補題の所属とファイルの責務を調査した。重点3項目すべての採否は上表に記す。今回の整理は `CLT-LOG`・`CLT-APPLY` の統合済み成果を対象とし、旧作業の未完成部分を実装する課題とは区別する。

純粋な整理では宣言名・型・仮定・結論・規格化を保持する。将来の利用だけを見込んだ抽象化、互換用別名、共有層から CLT への逆依存は導入しない。ガウス基盤の `aesop`・`grind` の整理は独立した保守課題として扱う。完了条件は、変更ファイルと利用側の検査、関連ビルド、共有層の変更時の既定ビルド、主要定理の公理依存と定理文の再照合である。

## 新たに一様な複素領域を必要とする場合

新しい利用側が一様な複素非零領域を必要とする場合は、[共有模型の現行結果と仮定](../Model/ARCHITECTURE.md#複素逆温度を扱う定理の仮定) を確認し、領域、行列の範囲、一様性を別課題として指定する。

## 新しい作業の仕様

短い依頼の扱いと引き渡しは [上位の規則](../AGENTS.md#短い依頼と分担範囲)、原稿の改訂と参照原稿の更新は [全体計画](../EDITING_PLAN.md#原稿改訂と実装の同期) に従う。作業IDは状態を二重管理するためではなく、この仕様と全体計画の割当を結び付けるために用いる。

各実装課題では担当範囲のコメント・ドキュメント文字列も確認し、原稿名・TeX ラベルを指定した版へ合わせる。文書・Blueprint の修正案は成果とともに統合担当へ渡す。共通の着手条件・引き渡し・検証記録は全体計画に集約し、この文書には課題固有の仕様と完了条件を記す。

モジュールの検索には [README の案内](README.md#finding-a-lemma) と [構造文書の索引](ARCHITECTURE.md#補助-lean-ファイルの役割) を使う。
