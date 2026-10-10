# SYK の未完了作業

この文書は未完了課題の状態と着手条件を管理する。規則は [AGENTS.md](AGENTS.md)、現行の数学的仕様は各構造文書、完了した成果と検証は [作業履歴](WORK_HISTORY.md) を参照する。Model と SuperConcentration に持ち越した実装課題はない。

## 残る作業

| 作業ID | 課題 | 状態・着手条件 | 担当・統合 |
| --- | --- | --- | --- |
| `CLT-CONVEX` | 各点収束から関数・導関数の局所一様収束を導く | 保留。再開時に対象と検証範囲を指定する | 未割当 |
| `CLT-EXTERNAL` | 引用元と `AnnealedInput` の構築に必要な外部入力の調査 | 保留。参照原稿・引用元の版を定めて読み取り調査する | 未割当 |
| `CLT-ANNEALED` | 明示した外部入力から `AnnealedInput` を構築する | 保留。上記調査後に外部仮定の採否・正確な型・編集範囲を確定する | 未割当 |
| `MAINT-UNUSED` | どこからも使われていない公開宣言の扱い | 第3分類の削除は完了。残る16件を削除するかの判断待ち | 未割当 |
| `MAINT-LINT` | linter の警告（519件、うちガウス基盤に506件）の解消 | 独立した保守課題。定理文が変わる9件は承認が要る。探索タクティク・非推奨 API・`maxHeartbeats` は整理済み | 未割当 |
| 公開の経路 | LICENSE と `lakefile.toml` のメタデータ、README の利用手順（`require` で使う方法）、リポジトリ名の確定、親の雛形なしでの `SYK`・`SYKBlueprint` 単体のビルドの CI、GitHub Pages での Blueprint 公開 | 保留。ライセンスの種類と公開範囲を共同研究者と決めてから着手する | 未割当 |

数学的仕様と完了条件は [CLT の計画](SYK/CLT/EDITING_PLAN.md) と [ガウス基盤の計画](SYK/Probability/GaussianConcentration/EDITING_PLAN.md) に記す。条件付き CLT と標準模型族への適用は検証済みだが、`hFE : AnnealedInput` の構築と `prop:annealed-free-energy` 自体の証明は未完了である。

公開の経路のうち GitHub Pages は、Verso Blueprint の雛形（`blueprint-pages.yml`）を土台にし、`Blueprint/` の直下で `lake exe cache get` と `lake exe vbp build` を実行して `Blueprint/_out/site/html-multi` を公開する。Pages の URL はリポジトリ名に依存するので、名前を確定してから設定する。

`CLT-CONVEX` と `CLT-EXTERNAL` は独立に調査できる。入力構築は必要な凸収束補題と外部入力の仕様を受け取って進める。並行候補の記載は複数エージェントの起動許可ではない。

## 保守課題

宣言の比較と走査の方法は [検証の補助](AGENTS.md#検証の補助) に記す。

### `MAINT-UNUSED`：使われていない公開宣言

研究者の方針は、Lean コードで使われておらず削除できる宣言は基本的に削除し、ライブラリを小さく保つことである。今でも有益な結果は、削除した内容と判断を作業履歴に残す。

`d5972da` での Lean の走査では、他の SYK 宣言から使われていない公開宣言が54件あった。第3分類のうち11件と、連鎖して不要になった宣言を削除した（[作業履歴](WORK_HISTORY.md#unused-declarations-2026-10-10)）。残る扱いは次のとおりである。

| 分類 | 件数 | 扱い |
| --- | --- | --- |
| 主定理と、Blueprint や文書が参照する入口 | 27 | 公開 API として残す |
| 原稿の `lem: parity rule lemma` の係数消滅に当たる一般の有限模型版 `expectation_partitionFunction_mul_hermite_eq_zero` | 1 | 判断待ち。残す場合は `CLT/ARCHITECTURE.md` の対応表に追記する |
| 参照のない小さな API（`normalizedTrace_add`・`normalizedTrace_zero`・`matrixTraceCLM_apply`・`expectation_eq_ofReal_re`・`gibbsState_eq_expectation_thermalDensity`・`realLogPartitionFunction`・`logPartition_upper_tail_of_beta_zero`・`logPartition_lower_tail_of_beta_zero`・`product_standardGaussian_lower_tail_zero`・`gaussianCouplings_eq_pi`・`polynomial_eval_mem_hermite_span`・`Schatten.normalizedNorm_nonneg`・`normalizedSchattenNorm_monotone`・`normalizedSchattenNorm_exp_hermitian`・`iterDirectionalFDeriv_traceExp_bound_of_norm_le_one`） | 15 | 判断待ち。上の方針では削除の候補になる |

完了条件は、残す宣言の位置付けが docstring か構造文書にあり、削除した宣言について宣言の比較・全体のビルド・Blueprint の検査・主要定理の公理依存の確認が済むことである。private 宣言は import 側の環境に現れないので、Lean の走査ではなく、宣言のあるファイル内の出現で調べる。

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

種類別の件数は `5772de4` の時点の値である。`MAINT-UNUSED` の削除後は合計519件で、ファイル別では `StandardGaussian` が257件、`Smooth` が174件、`Lipschitz` が75件、残り13件は行列解析・CLT・Model の数ファイルにある。ガウス基盤の部分の詳細は [ガウス基盤の計画](SYK/Probability/GaussianConcentration/EDITING_PLAN.md) に記す。1ファイルを1コミットの単位とし、機械的なもの（`longLine`、`unusedSimpArgs`、`refine'`）から先に行う。完了条件は、変更したファイルの個別検査と `lake build SYK` が成功し、宣言の型が完全に一致し（承認した仮定の削除を除く）、警告の件数が減ったことを確かめることである。

着手の順序は `MAINT-UNUSED` を先にし、量の多い `MAINT-LINT` を後にする。`MAINT-LINT` はほかと独立に進められる。行列解析の副名前空間の廃止（`MAINT-NAMESPACE`・`MAINT-ROOT`）は完了した（[作業履歴](WORK_HISTORY.md#matrix-namespace-2026-10-10)）。
