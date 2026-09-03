# AGENTS.md

## 適用範囲

このファイルは `SYK/` 以下の数学研究に適用する。workspace ルートの `AGENTS.md` にある Lean・Lake・検証の一般規則も引き続き適用する。`SYK/CLT/` などにさらに局所的な `AGENTS.md` がある場合は、それも併せて読む。

## プロジェクトの目的

このプロジェクトは Sachdev--Ye--Kitaev model の数学的研究を行う。基本的な作業サイクルは、数学的主張の定式化、非形式的証明または証明計画の作成、必要に応じた論文形式での記述、Lean 4 による形式化、Lean の検証結果に基づく再検討である。

定理文が意図した SYK の数学を表現しているかについては人間の研究者が最終的な責任を持つ。Codex は証明計画、文献と定義の対応、mathlib の探索、Lean 実装、error 分析、および局所的な検証を支援する。

## 話題ごとの独立性

`SYK/` 直下のサブディレクトリは、原則として別々の数学的話題または研究課題を表す。同じ Lake workspace と mathlib cache を共有することは、数学的依存関係を意味しない。

話題をまたぐ結果の利用では、数学的に必要な依存関係、Lean における明示的な `import`、normalization と仮定の一致、および循環依存がないことを確認する。

## 外部文献の利用

文献から結果を利用するときは、可能な限り使用箇所、原文の normalization、このリポジトリの normalization への変換、parameter range、正則性の仮定、convergence mode、および直接引用した結論と推論した結論の区別を記録する。

文献が与える範囲より強い収束、仮定、または温度領域を暗黙に採用しない。

## SYK の規約

次を黙って変更しない。

- Majorana generator の normalization
- normalized trace と unnormalized trace の区別
- Hamiltonian の variance normalization
- Gibbs exponential の符号
- interaction order の parity 条件
- Majorana fermion 数と large-`N` subsequence
- inverse-temperature regime

異なる文献またはディレクトリ間で規約が異なる場合、結果を移す前に変換を明示する。

## LaTeX と Lean の関係

- LaTeX 原稿は意図した数学的主張と論証を記録する。
- Lean は実際に記述された定義と定理文だけを検証する。
- 仮定、normalization、量化、型、結論を明示的に照合するまでは、Lean theorem が論文の theorem を検証したと述べない。
- 未形式化の解析的結果を named external input として切り出す場合、その状態を明記する。
- external input または conditional theorem を、内部で証明済みの事実として表現しない。

## プロジェクト文書

大きな証明課題では、必要に応じて対象ディレクトリに、公開用の案内を記す英語の `README.md`、Codex と研究者が依存関係を共有する日本語の `ARCHITECTURE.md`、未完了作業を管理する日本語の `EDITING_PLAN.md` を置く。

文書数は最小限に保ち、一つの文書で十分に代替できる status、issue、履歴用ファイルを機械的に増やさない。
