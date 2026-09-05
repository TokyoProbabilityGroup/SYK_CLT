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

再設計する共有 SYK 模型では、複素温度を扱う解析層に `z : ℂ`、物理的な Gibbs state と確率論的結果に
`β : ℝ≥0` を使用し、両者を同じ parameter field に格納しない。複素 partition
function の零点なし、holomorphic logarithm、positivity を暗黙に仮定しない。
normalized trace を標準とし、raw trace を使う場合は dimension factor を明示する。
