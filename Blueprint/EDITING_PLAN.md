# Blueprint 各章の編集計画

## 担当範囲

この文書は、このディレクトリの `Model.lean`、`GaussianConcentration.lean`、`SuperConcentration.lean`、`CLT.lean` に記す主要な主張と Lean 宣言の対応を管理する。全体の実行順序・状態・並行作業の可否は [全体計画](../EDITING_PLAN.md)、守る条件は [SYK の作業規則](../AGENTS.md) の Blueprint の節を参照する。

各章の更新は対応する実装単位に含める。ここでは上流の数学的な証明を再実装せず、未実装の宣言を実装済みとして参照しない。本文は公開用の英語で記述する。

章の編集は全体計画で指定した統合担当一人が行う。分担者は修正案を提出し、統合担当がコードの統合・検証と原稿照合を終えた範囲について証明状態・宣言参照・依存関係を更新する。Lean に残る外部仮定と `sorryAx` は内部証明と区別する。

## 現行の章と残件

`Model.lean`、`GaussianConcentration.lean`、`SuperConcentration.lean` は共有模型と集中評価の検証済み宣言を参照する。`Model.lean` は Z01 の局所非零円板と主値対数の正則性も参照する。`CLT.lean` は有限模型、ガウス–エルミート展開、高次剰余、および三種類の条件付き CLT をまとめた定理と個別定理を参照する。三つの主 CLT は `0<|β|<β_q` に限定し、`AnnealedInput` の構築を内部証明として扱わない。Gaussian `AnnealedInput` は CLT 章で仮定として明示する。

CLT 原稿と章・Lean 宣言の対応はソース上で照合済みである。`CLT-INPUT` の入力整理に伴うアニール入力の説明は、現在の `CLT.lean` に保持する。現在の対応と未形式化部分は [CLT の構造文書](../SYK/CLT/ARCHITECTURE.md#現行原稿の主張)、照合した版と検証結果は [監査記録](../WORK_HISTORY.md#clt-audit-2026-10-04) と [入力整理の記録](../WORK_HISTORY.md#clt-input-2026-10-04) を参照する。対応状況と残る修正は次のとおりである。

- 対数の期待誤差の明示的評価と、`prop:annealed-free-energy` を仮定した標準模型族への適用は実装・検証を終え、`CLT.lean` の数学的主張、宣言参照、残る仮定を更新した。[完了記録](../WORK_HISTORY.md#clt-log-apply-completion-2026-10-05) を参照する。`lem:convex-derivatives` の補完と命題自体の証明は保留し、再開・実装した場合に同様に更新する。命題を仮定した結果を無条件の主定理として記さない。
- `CLT-REFACTOR` では `CLT.lean` に有限ガウス二乗観測量と独立和の四次モーメントの節を追加し、二次 CLT と対数中心化誤差の依存を分けた。移設宣言の名前は保持し、Hermite 基本定義と二次観測量を明示 import した。数学的な主張と宣言・依存名はソース上で照合した。当時は Verso が休止中だったため、機械的検査は未実施だった。作業状態は [全体計画](../EDITING_PLAN.md#残る作業)、数学的な仕様は [CLT の計画](../SYK/CLT/EDITING_PLAN.md) を参照する。

- `CLT-CLEANUP` では分配 CLT の節の参照を個別定理に限定し、対数 CLT の節で結合定理の共通半径と射影の証明依存を説明する。数学的主張は保持し、章はソース上で照合する。

`REPO-LAYOUT` では4章を平坦な Blueprint に移し、Gaussian `AnnealedInput` の節を CLT 章へ保持した。4章・本文・生成入口の Lean 検査、HTML/PDF 生成と参照検査は成功した。結果と残る仮定は [構成変更の記録](../WORK_HISTORY.md#repo-layout-2026-10-07) に記す。

## 原稿改訂への対応

原稿のどの箇所の改訂でも [全体計画の同期手順](../EDITING_PLAN.md#原稿改訂と実装の同期) に従う。統合担当は改訂された主張・証明・引用と、[CLT 原稿との対応](../SYK/CLT/ARCHITECTURE.md#原稿改訂と実装の対応) を確認し、章の説明・依存関係・TeX ラベル・Lean 宣言との対応を更新する。原稿の記号変更だけを理由に Lean 宣言の改名を要求しない。

実装の証明状態を変えない記法・参照の修正は、原稿との対応確認後に反映してよい。未統合の実装を検証済みとして記載する変更とは区別する。改訂中または未照合の差分が残る場合は、照合した原稿の範囲と未確認箇所を明記する。

## 検証と記録

変更した章の数学的主張・Lean 宣言名・依存名を照合し、関係する章・`Main.lean`・`Build.lean` を Lean で検査する。HTML を生成して `vbp check` を実行し、対応する TeX 環境が利用可能なら任意で PDF も生成する。`VERSO-RESTORE` で休止中の変更を含む全5章と両入口の Lean 検査、HTML/PDF 生成と参照検査を終えた。結果は [復帰検証の記録](../WORK_HISTORY.md#verso-restore-2026-10-07) を参照する。独立した Annealed_FE 章は削除し、入力の構築を内部証明として扱わない。分担者の修正案を統合担当が直列に反映する。

検証記録は [全体計画](../EDITING_PLAN.md#識別情報と検証対象の記録) に従い、章では照合した宣言と未解決の参照も記録する。過去の検証結果と旧コマンドは [作業履歴](../WORK_HISTORY.md#chapters-records) を参照する。
