# SYK 中心極限定理の編集計画

## 目的と管理範囲

この文書は `refs/CLT_SYK.tex` と `refs/sections/` から成る原稿の修正、数学的監査、および Lean 形式化の作業順序と完了条件を管理する。

最小構成を維持するため、独立した `issue_register.md` は作成せず、既知の問題をこの文書で管理する。`decision_log.md` と `work_log.md` も作成せず、重要な判断理由は該当項目または `ARCHITECTURE.md` に反映する。

## Phase 0: 運用文書の整備

- [x] 共有 Lean workspace 用 `AGENTS.md` を一般化する。
- [x] `SYK/workspace/AGENTS.md` を配布用テンプレートとして追加する。
- [x] `SYK/AGENTS.md` と `SYK/CLT/AGENTS.md` を追加する。
- [x] `SYK/CLT/ARCHITECTURE.md` と本計画を追加する。
- [x] 公開用の英語版 `SYK/workspace/README.md` と `SYK/CLT/README.md` を追加する。

完了条件：source of truth、依存関係、未完了事項、および文書の役割分担が明示されている。

## Phase 1: 数学的内容を変えない原稿整理

- [ ] Gaussian-chaos expansion にある未完成の等号を修正する。
- [ ] Lemma 3.1 と Corollary 1.3 の証明にある重複を削除する。
- [ ] `paritcular` などの明らかな spelling error を修正する。
- [ ] 文脈上明白な `ell_p` と `ell'` の notation error を精査する。
- [ ] 長いコメントアウト済み旧証明を残すか削除するか決める。
- [ ] LaTeX 生成物を version control に含める方針を確認する。
- [ ] 原稿を compile し、error、warning、未解決参照を報告する。

完了条件：定理文の数学的内容を変更せず、原稿が重複や壊れた式なしに compile される。

## Phase 2: 定理文レベルの問題

この phase の変更は人間の研究者の明示的な承認後に行う。

- [ ] relative CLT の `beta = 0` における退化極限と、そこで未定義な standardized CLT の parameter range を分離する。
- [ ] Theorem 1.1--1.2、Corollary 1.3 と内部補題の温度領域を `beta >= 0` に統一する。
- [ ] 非負領域で `ell_q'(beta) > 0` を使う正確な nondegeneracy range を記述する。
- [ ] `beta_FE`、`beta_Rad`、nondegeneracy range、および Theorem 1.1 の range の関係を明記する。候補となる関係 `beta_q <= min(beta_FE, beta_Rad, beta_nd, tilde_beta_q)` が実際の依存関係を正しく表すか確認する。
- [ ] Theorem 1.1 を内部で証明するか、外部の quenched result を引用するか決定する。

完了条件：三つの主結果の temperature range と nondegeneracy condition が相互に整合する。

## Phase 3: Theorem 1.2 の監査

- [ ] Clifford sign-gauge action と incidence-parity rule を検証する。
- [ ] first chaos の消滅と exact second-chaos coefficient の normalization を検証する。
- [ ] iterated Duhamel formula と noncommutative Holder estimate を検証する。
- [ ] Rademacher encoding identity と exponential-moment estimate の一様性を検証する。
- [ ] `O(N^(-3(q/2-1))) = o(N^(2-q))` を確認する。
- [ ] annealed free-energy result の引用箇所、normalization conversion、analyticity の導出を確認する。
- [ ] variance asymptotic と standardized CLT の論理を確認する。

完了条件：現稿内の結果と明示した外部入力だけで Theorem 1.2 が閉じる。

## Phase 4: Theorem 1.1 の完成

- [ ] 必要な quenched/annealed comparison lemma を正確に定式化する。
- [ ] 既存の Gaussian concentration lemma が与える tail bound を整理する。
- [ ] `E[log Z_N]-log E[Z_N]` の必要な評価を証明または引用する。
- [ ] almost-sure convergence に十分な summable tail estimate を導く。
- [ ] Borel--Cantelli または適切な外部定理を用いて almost-sure statement を証明する。
- [ ] Theorem 1.1 の明示的な proof を原稿へ追加する。

完了条件：Theorem 1.1 の両方の極限が、明示された仮定と依存関係から証明される。

## Phase 5: Corollary 1.3 の監査

- [ ] probabilistic logarithmic linearization を検証する。
- [ ] negative tail の uniform-integrability argument を検証する。
- [ ] `E[log Y_N] = o(N^(1-q/2))` を検証する。
- [ ] `beta = 0` の扱いが standardized CLT に依存していないことを確認する。

完了条件：random linearization error と deterministic centering error がともに CLT scale で negligible である。

## Phase 6: Lean 形式化

既存 skeleton の theorem-label grouping を維持し、file/module component は
`UpperCamelCase`、namespace は `SYK.CLT` とする。README に存在しない module を掲載しない。

- [ ] `lemmas/` を `Lemmas/` へ改名し、全 import を同時に更新する。
- [ ] Lean comment と docstring が theorem number でなく TeX label を参照することを確認する。

形式化の候補順序は、incidence-even combinatorics、Rademacher encoding identity、remainder に必要な指数比較、abstract second-chaos-plus-remainder CLT transfer、logarithmic transfer lemmas、SYK 固有の finite model と matrix-analytic inputs である。

- [ ] `SYK.SYKModel` の complex `partitionFunction (z : ℂ)` を使用する。
- [ ] entire 性・複素微分と、`β : ℝ≥0` の positivity・確率結果を分離する。
- [ ] Lemma 3.3 は `SYK.SuperConcentration` の MGF と片側 tail を係数の損失なしに使う。
- [ ] complex logarithmic derivative の `Z z ≠ 0` を conditional input として明示する。

各段階で exact paper statement との対応、外部入力、Lean kernel による検証範囲を記録する。

完了条件：作成した各 Lean theorem が placeholder なしに検査され、重要な最終 theorem の `#print axioms` 結果が報告されている。

## Deferred: Complex zero-free region

- [ ] CLT の複素解析に必要な disk または strip を確定する。
- [ ] 一様 zero-free estimate を内部で証明するか外部結果を利用するか決定する。
- [ ] 証明済み領域上で logarithmic derivative の `Z z ≠ 0` 仮定を供給する。

全複素平面での zero-free 性や complex Gibbs positivity は目標にしない。

## 後から分離する可能性のある文書

現時点では次を作成しない。

- `proof_status.md`：結果数が増えて `ARCHITECTURE.md` の状態記述で管理できなくなった場合に分離する。
- `issue_register.md`：issue が増えて本計画の phase 別管理では追跡できなくなった場合に分離する。
- `decision_log.md`：重要な設計変更が増え、現在の文書から判断理由を追えなくなった場合に追加する。
- `work_log.md`：Git 履歴と本計画では作業履歴が不足する場合に限り追加する。
