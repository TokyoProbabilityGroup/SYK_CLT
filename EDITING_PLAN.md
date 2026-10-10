# SYK の未完了作業

この文書は未完了課題の状態と着手条件を管理する。規則は [AGENTS.md](AGENTS.md)、現行の数学的仕様は各構造文書、完了した成果と検証は [作業履歴](WORK_HISTORY.md) を参照する。Model と SuperConcentration に持ち越した実装課題はない。

## 残る作業

| 作業ID | 課題 | 状態・着手条件 | 担当・統合 |
| --- | --- | --- | --- |
| `CLT-CONVEX` | 各点収束から関数・導関数の局所一様収束を導く | 保留。再開時に対象と検証範囲を指定する | 未割当 |
| `CLT-EXTERNAL` | 引用元と `AnnealedInput` の構築に必要な外部入力の調査 | 保留。参照原稿・引用元の版を定めて読み取り調査する | 未割当 |
| `CLT-ANNEALED` | 明示した外部入力から `AnnealedInput` を構築する | 保留。上記調査後に外部仮定の採否・正確な型・編集範囲を確定する | 未割当 |
| 公開の経路 | LICENSE と `lakefile.toml` のメタデータ、README の利用手順（`require` で使う方法）、親の雛形なしでの `SYK`・`SYKBlueprint` 単体のビルドの CI、GitHub Pages での Blueprint 公開 | 保留。ライセンスの種類と公開範囲を共同研究者と決めてから着手する | 未割当 |

数学的仕様と完了条件は [CLT の計画](SYK/CLT/EDITING_PLAN.md) に記す。条件付き CLT と標準模型族への適用は検証済みだが、`hFE : AnnealedInput` の構築と `prop:annealed-free-energy` 自体の証明は未完了である。

公開の経路のうち GitHub Pages は、Verso Blueprint の雛形（`blueprint-pages.yml`）を土台にし、`Blueprint/` の直下で `lake exe cache get` と `lake exe vbp build` を実行して `Blueprint/_out/site/html-multi` を公開する。Pages の URL はリポジトリ名 `SYK_CLT` に依存する。

`CLT-CONVEX` と `CLT-EXTERNAL` は独立に調査できる。入力構築は必要な凸収束補題と外部入力の仕様を受け取って進める。並行候補の記載は複数エージェントの起動許可ではない。
