# SYK の未完了作業

この文書は未完了課題の状態と着手条件を管理する。規則は [AGENTS.md](AGENTS.md)、現行の数学的仕様は各構造文書、完了した成果と検証は [作業履歴](WORK_HISTORY.md) を参照する。Model・SuperConcentration・CLT に持ち越した実装課題はない。

## 残る作業

| 作業ID | 課題 | 状態・着手条件 | 担当・統合 |
| --- | --- | --- | --- |
| `MAINT-RING` | `ring` が失敗して `ring_nf` に退避する info 20 件の整理。`ring_nf` が目標を閉じる箇所だけ `ring_nf` に置換し、後続のタクティクが正規形に依存する箇所は書き方を変える。`gaussianReal_stein` 内の 13 件は証明の書き直しで解消済みで、残りは `StandardGaussian` 1 件・`Smooth` 4 件・`Lipschitz` 2 件 | `Smooth`・`Lipschitz` の書き換え案は一時ファイルで通過。完了条件：該当ファイルの info が 0 件 | 未割当 |
| `MAINT-BP-LINT` | Blueprint の `CLT.lean` に `set_option linter.mathlibStandardSet false` がなく 68 件、構造体フィールドの説明不足が 15 件の警告を出している | 未着手。完了条件：`lake build SYKBlueprint` の警告が依存パッケージ由来の 2 件だけになる | 未割当 |
| `BLUEPRINT-PAGES` | GitHub Pages での Blueprint 公開 | 検証 CI と独立した公開 workflow を準備済み。研究者による main への反映、Pages の Source 設定、初回 build・deploy と公開 URL の確認待ち | 研究者が反映・確認 |
| 公開の経路 | `lakefile.toml` のメタデータ、README の利用手順（`require` で使う方法）、親の雛形なしでの `SYK`・`SYKBlueprint` 単体のビルドの CI | 保留。ライセンスと引用情報は [README](README.md#licensing-and-citation)、[LICENSE](LICENSE)、[原稿の著作権表示](Paper/COPYRIGHT.md)、[CITATION.cff](CITATION.cff) に設定済み。残る公開手順は別課題とする | 未割当 |

CLT は `hFE : AnnealedInput` を明示的に仮定する形で仕様を確定した。条件付き CLT と標準模型族への適用は検証済みであり、入力の構築と `prop:annealed-free-energy` 自体の証明は作業範囲に含めない。数学的仕様は [CLT の構造文書](SYK/CLT/ARCHITECTURE.md) に記す。以前の保守課題（行列解析の副名前空間、未使用宣言、linter の警告）は完了した（[作業履歴](WORK_HISTORY.md#lint-2026-10-10)）。`Smooth.lean` の分割と `gaussianReal_stein` の証明の書き直しは完了した（[作業履歴](WORK_HISTORY.md#smooth-split-2026-10-11)、[作業履歴](WORK_HISTORY.md#stein-proof-2026-10-11)）。上の `MAINT-*` は、その後の調査で見つけた残件である。

`BLUEPRINT-PAGES` は `blueprint-pages.yml` を検証専用の `lean_action_ci.yml` から分離した。両者は親ワークスペースを使って独立にビルドし、公開 workflow は `lake build SYKBlueprint`、HTML 生成、`vbp check` の成功後に `SYK_CLT/_out/site/html-multi` を公開する設定を準備した。旧案の単体パッケージ方式には切り替えない。現行設定は [公開 workflow](.github/workflows/blueprint-pages.yml) を参照する。`Blueprint/README.md` は研究者向けの作業手順書であり、公開ファイルには含めない。その不在は公開前の残務として扱わない。完了条件は main での build・deploy の成功と公開ページの章・グラフ・検索・宣言リンクの確認。実行環境の制限により GitHub 側の状態は未確認である。Pages の URL はリポジトリ名 `SYK_CLT` に依存する。
