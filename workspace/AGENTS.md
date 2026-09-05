# AGENTS.md

## 適用範囲

このディレクトリは、複数の数学研究プロジェクトが一つの Lean 4 環境を共有するための統一的な Lean workspace である。

このファイルには数学分野に依存しない共通規則だけを置く。サブディレクトリで作業する際は、そのディレクトリまでの経路にあるすべての `AGENTS.md` を読み、上位の一般規則に下位の個別規則を追加して適用する。

## 共有 Lean workspace

- ルートの `lakefile.toml`、`lake-manifest.json` および `lean-toolchain` を全サブプロジェクトで使用する。
- `.lake/` は version control や配布の対象ではなく、Lake が workspace ルートに生成するローカル cache として扱う。
- 明示的な指示がない限り、サブプロジェクト内に別の Lake project、独立した dependency cache、mathlib のコピー、または `lean-toolchain` を作らない。
- 新しい数学プロジェクトは、原則としてルートの Lake workspace に Lean library または namespace として追加する。
- 依存パッケージの追加・更新、または `lakefile.toml`、`lake-manifest.json`、`lean-toolchain` の変更前に、理由と workspace 全体への影響を説明し、承認を得る。
- 必要がない限り、依存キャッシュ全体の再取得や全再ビルドを行わない。

## 数学的正しさ

- 明示的な指示がない限り、定理文の仮定、量化順序、型、結論を変更しない。
- 定理が偽、曖昧、または形式化に不適切である可能性を見つけた場合、黙って弱めたり修正したりせず、問題点を報告する。
- 非形式的な議論、数値・数式処理による計算、外部文献からの入力、および Lean kernel が検査した証明を明確に区別する。
- 正確な定理文について placeholder のない証明を Lean が受理するまでは、形式的に証明済みと述べない。

## Lean の証明

- `sorry`、`admit`、`axiom`、または同等の未検証な仮定を導入しない。
- 目標定理そのもの、その同値な言い換え、または循環する依存関係を証明に使用しない。
- `intro`、`exact`、`apply`、`refine`、`constructor`、`cases`、`induction`、`rw`、`have`、`calc` など、明示的な証明項と基本的な tactic を優先する。
- `simp`、`ring`、`norm_num`、`linarith` などの自動化は、数学的役割が明確な局所的な subgoal に限って使用する。
- 明示的に依頼されない限り、`aesop` や `grind` などの広範な証明探索を使用しない。
- 使用する主要な補題と、その数学的役割を説明する。

## 編集規則

- 現在の課題に必要な最小限の変更だけを行う。
- 研究上必要な範囲を超えて定義や定理を一般化しない。人間が読める主張を優先する。
- 明示的な依頼または管理上の必要がない限り、新しいファイルやディレクトリを作らない。
- 明示的に依頼されない限り、Git の commit、reset、rebase、既存変更の破棄を行わない。
- ユーザーによる無関係な変更を保持する。
- 編集後には関係する差分を確認し、変更内容を要約する。

## 検証

単一の Lean ファイルを変更した場合は、workspace ルートから次を実行する。

```bash
lake env lean path/to/ModifiedFile.lean
```

Lean library に影響する変更では、利用可能なら最小の関連 build target を実行する。workspace 全体に関わる変更の完了前には次を実行する。

```bash
lake build
```

残っている error、関連する warning、placeholder、未解決の goal、未検証の仮定をすべて報告する。重要な最終定理では `#print axioms` を用いて公理依存を確認し、その結果を報告する。

build の成功は Lean がコードを受理したことを意味するが、形式化された定理文が意図した数学を正しく表現することまでは保証しない。

## 自明でない証明の作業手順

1. 証明する定理を正確に言い直す。
2. 曖昧な点と反例になり得る場合を確認する。
3. 既存の定義と補題を調査する。
4. 編集前に短い証明計画を提示する。
5. 一度に一つの補題、または範囲を限定した一つの変更を扱う。
6. 意味のある変更ごとに Lean を実行する。
7. 方針が失敗した場合、大きな変更に進む前に Lean の error と数学的障害を説明する。

## Lean の命名

新規作成または再設計で改名する Lean module component と file は `UpperCamelCase`、type・structure・class、および `Prop` を返す predicate は `UpperCamelCase`、通常の値と関数は `lowerCamelCase`、theorem・lemma・proof field は mathlib の規則に従う `snake_case` とする。既存 declaration を theorem 名に含める場合は、その `lowerCamelCase` を一つの name atom として保持する。

この規則を理由に、現在の課題と無関係な既存 project や module を一括改名しない。

## Lean コードの設計

- 数学的内容を直接読める具体的な定義と定理を既定とする。
- 複数箇所で実際に再利用する場合、循環依存を避ける場合、または模型に依存しない結果を明確に分離する場合に限り抽象化する。
- 単一用途の typeclass、wrapper、alias、bridge lemma、module layer を予防的に追加しない。
- `import` は declaration が実際に必要とする最小の module に限定する。
- 依存を減らすために同じ数学的定義を重複させず、共有すべき定義は最も低い適切な layer に一度だけ置く。
- 抽象化を導入するときは、その具体的な consumer または依存関係上の利点を説明する。
- 将来の再利用可能性のための抽象化よりも、現在の数学的議論との対応と人間による可読性を優先する。

## LaTeX と Lean の関係

- LaTeX 原稿は意図した数学的主張と論証を記録する。
- Lean は実際に記述された定義と定理文だけを検証する。
- 仮定、normalization、量化、型、結論を明示的に照合するまでは、Lean theorem が論文の theorem を検証したと述べない。
- 未形式化の解析的結果を named external input として切り出す場合、その状態を明記する。
- external input または conditional theorem を、内部で証明済みの事実として表現しない。

## プロジェクト文書

大きな証明課題では、必要に応じて対象ディレクトリに、公開用の案内を記す英語の `README.md`、Codex と研究者が依存関係を共有する日本語の `ARCHITECTURE.md`、未完了作業を管理する日本語の `EDITING_PLAN.md` を置く。

文書数は最小限に保ち、一つの文書で十分に代替できる status、issue、履歴用ファイルを機械的に増やさない。

三つ以上の layer、分岐・合流、または複数 consumer を含む依存関係は、原則として Mermaid の `flowchart` で記述する。正確な theorem statement、仮定、型、定数、数式は diagram に埋め込まず、Markdown table、code block、または本文に記録する。単純な一方向の関係に diagram を追加しない。

## 言語方針

- ユーザーとの会話は、問い掛けが日本語なら日本語、英語なら英語で行う。
- Codex の設定、作業計画、進捗、依存関係、問題管理のための文書は日本語で記述する。これには `AGENTS.md`、`ARCHITECTURE.md`、`EDITING_PLAN.md` および同種の内部文書を含む。
- GitHub 等で外部公開される `README.md`、Lean コード、Lean 内のコメントと docstring、LaTeX 論文、および公開用研究成果物は英語で記述する。
- Markdown の言語は拡張子ではなく用途で決める。Codex との協働用文書は日本語、公開用文書は英語とする。
- Lean、mathlib、Lake、Git、API の正式な識別子・コマンド・用語は翻訳しない。
- 数学的主張を翻訳するときは、量化順序、仮定、記号、型、結論の強さを変更しない。
- 翻訳に数学的な曖昧さがある場合は、勝手に決定せず報告する。
