# SYK 分配関数の対数に対する集中不等式の編集計画

## 現在の作業

W02–W05 に残る実装課題はない。現行の宣言、依存関係と定数は [構造文書](ARCHITECTURE.md) および Lean ソースを参照する。各単位の移設・ビルド・公理依存の記録は [作業履歴](../WORK_HISTORY.md#gaussian-foundation)、[W03](../WORK_HISTORY.md#super-w03)、[W04](../WORK_HISTORY.md#super-w04)、[W05](../WORK_HISTORY.md#super-w05) に保存した。

新しい利用先や共有 API の変更が必要になった場合は、抽象 `MajoranaSystem` で成り立つ結果と標準行列表現に固有の結果を分けて仕様を定める。変更した Lean ファイルの個別検査と `lake build Model SuperConcentration`、主要定理の公理依存確認を行う。
