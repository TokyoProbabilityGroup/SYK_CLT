# SYK 分配関数の対数に対する集中不等式の編集計画

## 現在の作業

W02–W05 に残る実装課題はない。現行の宣言、依存関係と定数は [構造文書](ARCHITECTURE.md) および Lean ソースを参照する。各単位の移設・ビルド・公理依存の記録は [作業履歴](../WORK_HISTORY.md#gaussian-foundation)、[W03](../WORK_HISTORY.md#super-w03)、[W04](../WORK_HISTORY.md#super-w04)、[W05](../WORK_HISTORY.md#super-w05) に保存した。

新しい利用先や共有 API の変更が必要になった場合は、抽象 `MajoranaSystem` で成り立つ結果と標準行列表現に固有の結果を分けて仕様を定める。変更した Lean ファイルの個別検査と `lake build Model SuperConcentration`、主要定理の公理依存確認を行う。

## 共有層のリファクタリングへの対応

[全体計画](../EDITING_PLAN.md#残る作業) の最終段階で、数学的実装を終えた CLT と共有層の責務・依存を見直す。SuperConcentration は共有 API の利用側として影響を確認し、必要な参照変更と関連ビルドを担当する。現行の対数 CLT に集中評価を必須入力として追加せず、既存の規格化、MGF・裾の定数と証明済みの結論を保持する。詳細な調査仕様は [CLT の計画](../CLT/EDITING_PLAN.md#数学的実装後のリファクタリング) に置く。
