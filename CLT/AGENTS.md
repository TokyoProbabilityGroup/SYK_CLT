# AGENTS.md

## 適用範囲

このファイルは `SYK/CLT/` 以下に適用する。workspace ルートおよび `SYK/AGENTS.md` の規則も引き続き適用する。

## 作業前に読む文書

CLT 原稿、証明構造、または Lean 形式化を変更する前に、次を確認する。

1. `ARCHITECTURE.md`
2. `EDITING_PLAN.md`
3. `refs/CLT_SYK.tex` と `refs/sections/` の関係箇所

## Source of truth

- `refs/CLT_SYK.tex` は現在の論文の root と共通 preamble を記録し、`refs/sections/` は本文を記録する。両者を合わせたものを定理文の source of truth とする。
- `ARCHITECTURE.md` は意図した証明依存関係と各結果の現在の状態を記録する。
- `EDITING_PLAN.md` は既知の問題、優先順位、作業の完了条件を記録する。
- Lean ファイルは、Lean kernel が検査した正確な定理文についてのみ証明状態を記録する。

これらが一致しない場合、黙って一つを選んだり統合したりせず、不一致を報告する。

## 保護する数学的内容

明示的な承認なしに、`M_N`、`sigma_N`、`H_N`、`Z_N`、`Y_N` の定義、scaling `N^(q/2-1)`、limiting variance、inverse-temperature range、relative・standardized・logarithmic CLT の区別、および各結果の convergence mode を変更しない。

今後の論文の確率論的主結果は `β ≥ 0` で述べる。Lean の共有模型では
`partitionFunction (z : ℂ)` を使い、entire 性、複素微分、展開など順序構造を必要としない
補題は可能な範囲で複素化する。positivity、real logarithm、Gaussian concentration、CLTは
`β : ℝ≥0` の specialization に限定する。

complex logarithmic derivative に現れる `Z z ≠ 0` は conditional hypothesis として明示し、
証明済みの zero-free region がない段階で自動的に満たされるものとして扱わない。

## 現在の証明構造

partition-function CLT は、sign-gauge incidence parity、Gaussian--Hermite integration by parts、first chaos の消滅と second chaos の厳密な同定、Duhamel derivative bound、Rademacher encoding と exponential-moment estimate、annealed free-energy derivative asymptotics、および classical i.i.d. CLT を使用する。

現在の higher-chaos remainder proof を説明するときは、`refs/sections/gaussian-chaos.tex` にある Rademacher encoding と exponential-moment estimate による直接評価を用いる。

log-partition CLT にはさらに、logarithmic linearization、Gaussian concentration、negative-tail control、および log-centering estimate が必要である。

Theorem 1.1 には、annealed limit とは別に almost-sure quenched/annealed comparison の明示的な証明が必要である。

## 既知の重要事項

作業前に `EDITING_PLAN.md` の未完了項目を確認する。特に現状では次が未解決である。

- Theorem 1.1 の完全な証明が原稿にない。
- standardized CLT は `beta = 0` で定義されない。
- 原稿には負の `beta` を含む旧 parameter range が残っており、非負実温度へ統一する必要がある。

これらの解決は定理文を変更し得るため、単なる誤植修正として処理せず、人間の研究者の承認を得る。

## Lean dependency

依存方向は `SYK.Probability.GaussianConcentration`、`SYK.SYKModel`、
`SYK.SuperConcentration` から `SYK.CLT` への一方向とする。CLT から共有 layer を再定義せず、
共有 layer が CLT を import する循環も作らない。module と file は `UpperCamelCase` とする。

Lean の comment と docstring では、`Theorem 1.2` や `Lemma 3.3` のような原稿編集で変わる
番号ではなく、TeX の `\label{...}` を backtick で囲んで参照する。対応する label がない
結果は勝手に命名せず、TeX に label を追加するか `currently unlabeled` と明記する。

## 文書の集約方針

最小構成を維持するため、独立した `proof_status.md`、`issue_register.md`、`decision_log.md`、`work_log.md` は現時点では作成しない。

- proof status は `ARCHITECTURE.md` に記録する。
- issue、優先順位、未完了項目は `EDITING_PLAN.md` に記録する。
- 重要な方針決定は、関係する上記文書の該当節に理由とともに反映する。

情報量が増えてこれらの文書では管理できなくなった場合に限り、役割を再分割する。
