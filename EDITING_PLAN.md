# SYK の未完了作業

この文書は未完了課題の状態と着手条件を管理する。規則は [AGENTS.md](AGENTS.md)、現行の数学的仕様は各構造文書、完了した成果と検証は [作業履歴](WORK_HISTORY.md) を参照する。数学コードの整備は完了しており、その判断と検証は [整備の記録](WORK_HISTORY.md#maint-audit-2026-10-13) に記す。

## 残る作業

| 作業ID | 課題 | 状態・着手条件 | 担当・統合 |
| --- | --- | --- | --- |
| `BLUEPRINT-PAGES` | GitHub Pages での Blueprint 公開 | 公開は CI の workflow の deploy job が行う（MA-14）。Pages の Source 設定、初回 build・deploy と公開 URL の確認待ち | 研究者が確認 |
| 公開の経路 | `lakefile.toml` のメタデータ、README の利用手順（`require` で使う方法）、親の雛形なしでの `SYK`・`SYKBlueprint` 単体のビルドの CI | 保留。ライセンスと引用情報は [README](README.md#licensing-and-citation)、[LICENSE](LICENSE)、[原稿の著作権表示](Paper/COPYRIGHT.md)、[CITATION.cff](CITATION.cff) に設定済み。残る公開手順は別課題とする | 未割当 |

## 補足

CLT は `hFE : AnnealedInput` を明示的に仮定する形で仕様を確定した。形式化の範囲は [CLT の構造文書](SYK/CLT/ARCHITECTURE.md#仮定する命題と形式化の範囲) に記す。

`BLUEPRINT-PAGES` の公開は、[CI の workflow](.github/workflows/lean_action_ci.yml) の deploy job が行う。Blueprint の job（`lake build SYKBlueprint`、HTML 生成、`vbp check`）に合格した `main` の `SYK_CLT/_out/site/html-multi` を公開する。旧案の単体パッケージ方式には切り替えない。完了条件は main での build・deploy の成功と、公開ページの章・グラフ・検索・宣言リンクの確認である。実行環境の制限により GitHub 側の状態は未確認である。Pages の URL はリポジトリ名 `SYK_CLT` に依存する。
