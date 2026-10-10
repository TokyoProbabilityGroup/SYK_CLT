# SYK の未完了作業

この文書は未完了課題の状態と着手条件を管理する。規則は [AGENTS.md](AGENTS.md)、現行の数学的仕様は各構造文書、完了した成果と検証は [作業履歴](WORK_HISTORY.md) を参照する。Model と SuperConcentration に持ち越した実装課題はない。

## 残る作業

| 作業ID | 課題 | 状態・着手条件 | 担当・統合 |
| --- | --- | --- | --- |
| `CLT-CONVEX` | 各点収束から関数・導関数の局所一様収束を導く | 保留。再開時に対象と検証範囲を指定する | 未割当 |
| `CLT-EXTERNAL` | 引用元と `AnnealedInput` の構築に必要な外部入力の調査 | 保留。参照原稿・引用元の版を定めて読み取り調査する | 未割当 |
| `CLT-ANNEALED` | 明示した外部入力から `AnnealedInput` を構築する | 保留。上記調査後に外部仮定の採否・正確な型・編集範囲を確定する | 未割当 |
| `MAINT-NAMESPACE` | 行列解析の副名前空間 `SYK.MatrixAnalysis.Matrix`・`LinearMap` の整理 | 判断待ち。[保守課題](#保守課題) の方針を決めてから着手する | 未割当 |
| `MAINT-ROOT` | `_root_` を使う宣言の位置の整理 | `MAINT-NAMESPACE` と同時に行う。見送る場合は単独で行える | 未割当 |
| `MAINT-UNUSED` | どこからも使われていない公開宣言の扱い | 判断待ち。確認表を作って、残すか削除するかを1件ずつ決める | 未割当 |
| `MAINT-LINT` | linter の警告（531件、うちガウス基盤に516件）の解消 | 独立した保守課題。定理文が変わる9件は承認が要る。探索タクティク・非推奨 API・`maxHeartbeats` は整理済み | 未割当 |
| 公開の経路 | LICENSE と `lakefile.toml` のメタデータ、README の利用手順（`require` で使う方法）、リポジトリ名の確定、親の雛形なしでの `SYK`・`SYKBlueprint` 単体のビルドの CI、GitHub Pages での Blueprint 公開 | 保留。ライセンスの種類と公開範囲を共同研究者と決めてから着手する | 未割当 |

数学的仕様と完了条件は [CLT の計画](SYK/CLT/EDITING_PLAN.md) と [ガウス基盤の計画](SYK/Probability/GaussianConcentration/EDITING_PLAN.md) に記す。条件付き CLT と標準模型族への適用は検証済みだが、`hFE : AnnealedInput` の構築と `prop:annealed-free-energy` 自体の証明は未完了である。

公開の経路のうち GitHub Pages は、Verso Blueprint の雛形（`blueprint-pages.yml`）を土台にし、`Blueprint/` の直下で `lake exe cache get` と `lake exe vbp build` を実行して `Blueprint/_out/site/html-multi` を公開する。Pages の URL はリポジトリ名に依存するので、名前を確定してから設定する。

`CLT-CONVEX` と `CLT-EXTERNAL` は独立に調査できる。入力構築は必要な凸収束補題と外部入力の仕様を受け取って進める。並行候補の記載は複数エージェントの起動許可ではない。

## 保守課題

`5772de4` の時点で調べた結果である。警告は全体ビルドのログから、未使用の宣言は Lean で全宣言の参照関係を走査して数えた。宣言の比較と走査の方法は [検証の補助](AGENTS.md#検証の補助) に記す。

### `MAINT-NAMESPACE`：行列解析の副名前空間

`SYK.MatrixAnalysis.Matrix`（公開名53件）と `SYK.MatrixAnalysis.LinearMap`（7件）は、mathlib の `Matrix`・`LinearMap` と同じ名前の副名前空間である。そのため次の問題がある。

- `namespace SYK.MatrixAnalysis` の中では `Matrix` が SYK 側に解決され、`open _root_.Matrix in` が要る（`SingularValues.lean`）。
- 型は mathlib の `Matrix` なので、`A.traceExp` のようなフィールド記法は使えない。それでも名前が `Matrix.traceExp` なので、mathlib の宣言と誤認しやすい。
- `SYK.MatrixAnalysis.Matrix.normalizedTrace`（一般の `RCLike`、空型も可）と Model の `SYK.normalizedTrace`（複素行列、非空型）は、短い名前が同じで定義が異なる。

推奨する解決方法は、2つの副名前空間を廃止し、宣言を `SYK.MatrixAnalysis` の直下へ移すことである。平らにしても名前は衝突しない。ただし `normalizedTrace` と `normalizedTrace_one` は Model の宣言と短い名前が同じなので、区別したければ改名する。外部の利用は `CLT/Chaos/PartitionDerivatives.lean` と `PartitionHigherDerivatives.lean` の約27か所だけで、Blueprint からの参照はない。話題を表す副名前空間（`DirectionalDerivative`、`Radial`、`Duhamel`、`Schatten`、`PositiveTrace`）は残す。

判断が必要な点は、平らにするかどうかと、`normalizedTrace` を改名するかどうかである。完了条件は、変更前後の全宣言の比較で改名の対応以外に型の違いがなく、`lake build SYKBlueprint`、生成と `vbp check`、主要定理の公理依存の確認が済むことである。

### `MAINT-ROOT`：`_root_` を使う宣言

- `TraceExpDerivatives.lean` の `contDiff_traceExp` は、private の局所インスタンス（`SMul ℝ`、`SMul 𝕜`、`IsScalarTower`）を使うため、`DerivAux` の中から `_root_` で宣言している。インスタンスを `Matrix.realNormedSpace` の隣へ移せば、通常の位置で宣言できる。
- `TraceExponential.lean` の `trace_exp_smul_of_isHermitian` は `ExpAux` の中にある。直後の `namespace Matrix` の区画へ移せばよい。
- `SingularValues.lean` の `open _root_.Matrix in` は `MAINT-NAMESPACE` で不要になる。

完了条件は `MAINT-NAMESPACE` と同じである。

### `MAINT-UNUSED`：使われていない公開宣言

公開宣言466件のうち、他の SYK 宣言から使われていないものが54件ある。

| 分類 | 件数 | 扱い |
| --- | --- | --- |
| 主定理と、Blueprint や文書が参照する入口 | 27 | 公開 API として残す |
| 参照はないが API として自然なもの（例：`normalizedTrace_add`、`logPartition_upper_tail_of_beta_zero`、`realLogPartitionFunction`） | 15 | 残す。必要なら docstring に位置付けを書く |
| 途中段階や原稿との対応用と思われるもの（例：`coord_stein_of_manuscript_growth`、`hermiteMulti_ibp_prod`、`fderiv_exp_apply`、`normalizedTrace_duhamel_kernel`、`expectation_partitionFunction_mul_hermite_eq_zero`） | 12 | 1件ずつ確認する |

どこからも使われていないので、`private` にしても意味がない。第3分類は、原稿の主張に対応するものを残して構造文書から参照し、役割を終えたものを削除する。削除は公開 API の変更なので、確認表を示して1件ずつ承認を得る。完了条件は、残す宣言の位置付けが docstring か構造文書にあり、削除した宣言について全体のビルドと Blueprint の検査が済むことである。

### `MAINT-LINT`：linter の警告

| linter | 件数 | 解決方法 |
| --- | --- | --- |
| `style.longLine` | 257 | 改行する |
| `style.refine`（`refine'`） | 121 | `refine` に改め、ゴールにする `_` を `?_` にする |
| `flexible`（後に続く柔軟な `simp`） | 80 | `simp?` の提案から `simp only [...]` に固定する |
| `style.multiGoal` | 34 | `·` でゴールを分ける |
| `unusedSimpArgs` | 25 | 示された引数を削除する |
| `unusedDecidableInType`・`unusedFintypeInType` | 9 | `omit [...] in` で外す。定理文の仮定が減るので承認が要る |
| `unusedVariables`、`style.show`、`unnecessarySimpa` | 5 | 個別に直す |

ファイル別では `StandardGaussian` が263件、`Smooth` が178件、`Lipschitz` が75件で、残り15件は行列解析と CLT の数ファイルにある。ガウス基盤の部分の詳細は [ガウス基盤の計画](SYK/Probability/GaussianConcentration/EDITING_PLAN.md) に記す。1ファイルを1コミットの単位とし、機械的なもの（`longLine`、`unusedSimpArgs`、`refine'`）から先に行う。完了条件は、変更したファイルの個別検査と `lake build SYK` が成功し、宣言の型が完全に一致し（承認した仮定の削除を除く）、警告の件数が減ったことを確かめることである。

着手の順序は、名前を公開前に確定させるため `MAINT-NAMESPACE` と `MAINT-ROOT` を先にし、次に `MAINT-UNUSED`、最後に量の多い `MAINT-LINT` とする。`MAINT-LINT` はほかと独立に進められる。
