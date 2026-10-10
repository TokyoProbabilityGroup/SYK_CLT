# SYK の未完了作業

この文書は未完了課題の状態と着手条件を管理する。規則は [AGENTS.md](AGENTS.md)、現行の数学的仕様は各構造文書、完了した成果と検証は [作業履歴](WORK_HISTORY.md) を参照する。Model と SuperConcentration に持ち越した実装課題はない。

## 残る作業

| 作業ID | 課題 | 状態・着手条件 | 担当・統合 |
| --- | --- | --- | --- |
| `CLT-CONVEX` | 各点収束から関数・導関数の局所一様収束を導く | 保留。再開時に対象と検証範囲を指定する | 未割当 |
| `CLT-EXTERNAL` | 引用元と `AnnealedInput` の構築に必要な外部入力の調査 | 保留。参照原稿・引用元の版を定めて読み取り調査する | 未割当 |
| `CLT-ANNEALED` | 明示した外部入力から `AnnealedInput` を構築する | 保留。上記調査後に外部仮定の採否・正確な型・編集範囲を確定する | 未割当 |
| `MAINT-LINT` | linter の警告（519件、うちガウス基盤に506件）の解消 | 独立した保守課題。定理文が変わる9件は承認が要る。探索タクティク・非推奨 API・`maxHeartbeats` は整理済み | 未割当 |
| `BLUEPRINT-PAGES` | GitHub Pages での Blueprint 公開 | 検証 CI と独立した公開 workflow・手順を準備済み。研究者による main への反映、Pages の Source 設定、初回 build・deploy と公開 URL の確認待ち | 研究者が反映・確認 |
| 公開の経路 | LICENSE と `lakefile.toml` のメタデータ、README の利用手順（`require` で使う方法）、親の雛形なしでの `SYK`・`SYKBlueprint` 単体のビルドの CI | 保留。ライセンスの種類と公開範囲を共同研究者と決めてから着手する | 未割当 |

数学的仕様と完了条件は [CLT の計画](SYK/CLT/EDITING_PLAN.md) と [ガウス基盤の計画](SYK/Probability/GaussianConcentration/EDITING_PLAN.md) に記す。条件付き CLT と標準模型族への適用は検証済みだが、`hFE : AnnealedInput` の構築と `prop:annealed-free-energy` 自体の証明は未完了である。

`BLUEPRINT-PAGES` は `blueprint-pages.yml` を検証専用の `lean_action_ci.yml` から分離した。両者は親ワークスペースを使って独立にビルドし、公開 workflow は `lake build SYKBlueprint`、HTML 生成、`vbp check` の成功後に `SYK_CLT/_out/site/html-multi` を公開する設定を準備した。旧案の単体パッケージ方式には切り替えない。手順と現行設定は [Blueprint の公開案内](Blueprint/README.md) を参照する。完了条件は main での build・deploy の成功と公開ページの章・グラフ・検索・宣言リンクの確認。実行環境の制限により GitHub 側の状態は未確認である。Pages の URL はリポジトリ名 `SYK_CLT` に依存する。

`CLT-CONVEX` と `CLT-EXTERNAL` は独立に調査できる。入力構築は必要な凸収束補題と外部入力の仕様を受け取って進める。並行候補の記載は複数エージェントの起動許可ではない。

## 保守課題

宣言の比較と走査の方法は [検証の補助](AGENTS.md#検証の補助) に記す。

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

種類別の件数は `5772de4` の時点の値である。`MAINT-UNUSED` の削除後も合計519件で、ファイル別では `StandardGaussian` が257件、`Smooth` が174件、`Lipschitz` が75件、残り13件は行列解析・CLT・Model の数ファイルにある。ガウス基盤の部分の詳細は [ガウス基盤の計画](SYK/Probability/GaussianConcentration/EDITING_PLAN.md) に記す。1ファイルを1コミットの単位とし、機械的なもの（`longLine`、`unusedSimpArgs`、`refine'`）から先に行う。完了条件は、変更したファイルの個別検査と `lake build SYK` が成功し、宣言の型が完全に一致し（承認した仮定の削除を除く）、警告の件数が減ったことを確かめることである。

`MAINT-LINT` はほかと独立に進められる。保守課題のうち、行列解析の副名前空間の廃止（`MAINT-NAMESPACE`・`MAINT-ROOT`）と使われていない宣言の削除（`MAINT-UNUSED`）は完了した（[副名前空間](WORK_HISTORY.md#matrix-namespace-2026-10-10)、[未使用宣言](WORK_HISTORY.md#unused-declarations-2026-10-10)）。
