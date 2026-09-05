# 共有 SYK 模型の編集計画

## 目的

現在の API との互換性を要求せず、normalized trace、complex analytic temperature、physical
nonnegative temperature、abstract/concrete Majorana layer を明確に分離する。

## Phase 0: Baseline と文書監査

- [ ] 現行 public symbols と consumer を列挙する。
- [ ] lecture notes、CLT TeX、`model.txt`、Lean source の相違を記録する。
- [ ] 現行 build と重要 theorem の axioms を記録する。

## Phase 1: Module と parameter

- [ ] `SYK_model` を `SYKModel` へ移し、file/module component を `UpperCamelCase` にする。
- [ ] `lakefile.toml` の target `SYK_model` を `SYKModel` へ改名し、理由と全 consumer への
  影響を説明してから変更する。
- [ ] temperature を model parameter から削除する。
- [ ] interaction index、canonical ordering、phase、abstract Majorana API を整理する。
- [ ] compatibility alias は作らない。

## Phase 2: Abstract algebra と standard realization

- [ ] phase-corrected interaction と canonical Hamiltonian を共有定義にする。
- [ ] even `N` の standard Jordan--Wigner matrix realization を構成する。
- [ ] dimension、CAR、self-adjointness、normalized-trace orthogonality を証明する。

## Phase 3: Complex matrix calculus

- [ ] raw trace と normalized trace を定義し、後者を標準にする。
- [ ] exponent matrix に対する normalized trace exponential を定義する。
- [ ] `partitionFunction (z : ℂ) H = tr(exp(-zH))` を specialization として定義する。
- [ ] `partitionFunction` が `rawPartitionFunction / card d` に definitionally 展開される
  定義配置にする。
- [ ] `Z(0)=1`、entire 性、複素微分公式を証明する。
- [ ] `Z z ≠ 0` の下で logarithmic derivative を証明する。

## Phase 4: Physical Gibbs layer

- [ ] `β : ℝ≥0` specialization の positivity を証明する。
- [ ] thermal density、Gibbs expectation、real log-partition を定義・検証する。
- [ ] raw/normalized Gibbs expectation と centered `log Z` の対応を証明する。

## Phase 5: Gaussian disorder と consumer migration

- [ ] `CouplingSpace`、canonical `σ_N`、standard Gaussian measure を共有模型に置く。
- [ ] 汎用 Gaussian concentration 定義を共有模型へ混入させない。
- [ ] `SuperConcentration` を新 API へ移行する。
- [ ] CLT interface を `SYK/CLT/ARCHITECTURE.md` と照合する。
- [ ] `Annealed_FE` は編集せず、既知の破損を正確に記録する。

## Deferred: Zero-free regions

- [ ] fixed Hamiltonian の real axis 近傍など、最初の具体的 zero-free theorem を選定する。
- [ ] high-temperature disk/strip の一様評価が必要か CLT と照合する。
- [ ] zero-free theorem から conditional logarithmic API の仮定を供給する。
- [ ] simply connected region 上の holomorphic logarithm を必要な場合だけ構成する。

`Z z ≠ 0` を全複素平面で証明すること、または complex Gibbs operator の positivity を
目標にしない。

## 検証条件

各 Lean file を個別に検査し、`lake build SYKModel SuperConcentration` を実行する。主要
theorem では `#print axioms` を確認する。新しい `sorry`、`admit`、`axiom`、未解決 goal は
許容しない。full build の failure は未移行の `Annealed_FE` に限定して報告する。
