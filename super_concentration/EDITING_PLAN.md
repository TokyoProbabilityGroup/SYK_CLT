# SYK super-concentration の編集計画

## Phase 0: Baseline

- [ ] 現行 theorem、axioms、build status、consumer を記録する。
- [ ] blueprint と Lean source の scale、path、proof status の相違を記録する。

## Phase 1: Generic Gaussian backend

- [ ] `SYK/Probability/GaussianConcentration/` を `UpperCamelCase` modules で構成する。
- [ ] SYK coupling definitions と `N,q` specialization を backend から除く。
- [ ] smooth proof、mollification、MGF theorem の最小 import graph を作る。
- [ ] tail corollary は mathlib の `HasSubgaussianMGF` API から導く。

完了条件：backend の statement と imports に SYK-specific data が現れない。

## Phase 2: Shared-model migration

- [ ] interaction と Gaussian coupling は `SYKModel` から importする。
- [ ] matrix trace-exponential と physical Gibbs calculus は `SYKModel` から importする。
- [ ] density-matrix estimate と Majorana sum-of-squares bound だけを残す。

## Phase 3: Concentration specialization

- [ ] `β : ℝ≥0` の log-partition derivative を証明する。
- [ ] exact Majorana boundから `β / sqrt q` Lipschitz estimate を導く。
- [ ] centered log-partition の `HasSubgaussianMGF` parameter `β^2/q` を証明する。
- [ ] lower、upper、two-sided tail を導く。
- [ ] `β=0` を normalized `Z(0)=1` から処理する。

完了条件：CLT の MGF と片側 tail を係数の損失なしに供給できる。

## Phase 4: Module migration と cleanup

- [ ] directory を `SuperConcentration`、files を `UpperCamelCase` に改名する。
- [ ] `lakefile.toml` の target `super_concentration` を `SuperConcentration` へ改名し、
  consumer と build command を同時に更新する。
- [ ] 旧重複 definitions、中間 public constants、一般 `𝒥` API を削除する。
- [ ] compatibility alias は作らない。
- [ ] Lean 安定後に README と blueprint を更新または historical と明示する。

## Verification

- [ ] 各変更ファイルを dependency order で `lake env lean` により検査する。
- [ ] `lake build SYKModel SuperConcentration` を実行する。
- [ ] MGF、片側 tail、二側 tail の定数を theorem statement で確認する。
- [ ] 主要 theorem の `#print axioms` を確認する。

`Annealed_FE` は編集対象外とし、新しい placeholder と同 project 以外の build error は
許容しない。
