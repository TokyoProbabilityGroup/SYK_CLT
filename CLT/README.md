# High-Temperature SYK Central Limit Theorem

This directory contains the manuscript and Lean formalization work for the central limit theorem governing high-temperature fluctuations of the SYK partition function and free energy.

## Current contents

- `FiniteModel.lean`: abstract finite Majorana partition functions, trace bounds, and Gaussian moment and logarithm estimates, with inputs `Params` and `MajoranaSystem`.
- `Basic.lean`: the asymptotic family API `Setting q` and the assumed annealed input `AnnealedInput q S`. `Main.lean` states the conditional CLTs.
- `StandardModel.lean`: the standard family of sizes `q + 2 * n`, its trace normalization, and the three conditional CLTs.
- `Normalization.lean`: the finite standard-representation check `partitionFunction_standard`; this module is not imported by the abstract CLT proofs.
- `refs/CLT_SYK.tex`: manuscript root containing the shared preamble, front matter, and references.
- `refs/sections/`: independently compilable top-level manuscript sections; together with the root file, these are the source of truth for the paper theorem statements.
- `ARCHITECTURE.md`: internal proof-dependency and status documentation.
- `EDITING_PLAN.md`: internal manuscript-audit and formalization plan.
- `AGENTS.md`: topic-specific instructions for Codex.

The internal planning documents are written in Japanese for collaboration between the researcher and Codex. Public mathematical artifacts, including this README, the manuscript, and Lean source files, are written in English.

## Finding a lemma

From the shared workspace root, start with a declaration name and its callers: `rg -n 'NAME' SYK/CLT SYK/Probability SYK/Model`. For an unfamiliar file, search its `theorem`, `lemma`, `def`, and `namespace` lines before reading proofs. Each lemma module's opening docstring lists its role and main entry points.

The principal import paths are:

| Task | Modules to inspect in order |
| --- | --- |
| Gaussian Hermite coefficients and completeness | `GaussianHermiteBasic` → `GaussianChaos` → `GaussianHermiteOrthogonality` → `GaussianHermiteDensity` and `GaussianMomentDetermination` → `GaussianPolynomialDensity` |
| Singular values and matrix derivatives | `SingularValues` → `MatrixTraceExponential` → `TraceExpDerivatives` |
| Finite SYK second chaos | `Basic`, `CliffordSignParity`, `GaussianHermiteOrthogonality` → `Preliminaries`; `TraceExpDerivatives` → `PartitionDerivatives`; both → `SecondChaos` |
| Independent estimates | `Rademacher` or `ConvexDerivatives` |
| Quadratic Gaussian moments and CLT | `GaussianQuadraticObservable` → `GaussianFourthMoment` → `IndependentFourthMoment`; `GaussianQuadraticObservable` and `SecondChaosAsymptotic` → `GaussianQuadraticCLT` |

`Preliminaries` imports `Basic` for `Setting`, `Z`, and `Y`. The general Gaussian Hermite integration-by-parts API used by the active CLT modules is in `Probability/GaussianConcentration/Smooth.lean`; search there before opening the large `GaussianIBP.lean`.

`GaussianHermiteBasic` contains the finite product Gaussian measure, Hermite products, and their sign/permutation identities. `GaussianChaos` uses these without importing the model-specific `CliffordSignParity`. Finite quadratic observables and their first two moments are in `GaussianQuadraticObservable`; fourth-moment estimates do not import the quadratic CLT.

## Current status

`FiniteModel.lean` defines the normalized Gaussian partition function for general finite-dimensional matrix Majorana systems. `Basic.lean` defines families of diverging even system sizes, the relative, standardized, and centered logarithmic fluctuations, and `AnnealedInput`. The three CLT statements in `Main.lean` take `{q : ℕ} (S : Setting q) (hFE : AnnealedInput q S)`; evenness and `q ≥ 4` are fields of `S`, with no duplicate arguments. `AnnealedInput` receives the assertions of the manuscript's `prop:annealed-free-energy` for `S`: an even convex `C¹` limit on the whole real line, locally uniform convergence of the normalized pressure and derivative, and `β ℓ_q'(β) > 0` at every nonzero real inverse temperature. `partition_and_log_partition_clt` states all three CLTs with one common radius for real `0 < |β| < βq`: the relative and centered logarithmic limits have variance `(q!/2) β² (ℓ_q'(β))²`, while the standardized limit has variance `1`. `partition_clt` proves the partition-function conclusion directly, and `log_partition_clt` gives the logarithmic conclusion. The proposition is assumed for `S`; proving it or constructing `hFE` is outside the conditional CLT proof.

`partition_and_log_partition_clt` and both individual CLT theorems are Lean-checked without `sorryAx`, conditional on `AnnealedInput`. The finite-model proofs establish tracelessness, `Z ≥ 1`, `partition_moments`, positivity and expectation one of `Y`, square integrability, integrability of both logarithms, and equality of their centered versions. Specialization to the standard representation gives the manuscript trace normalization. The finite-model results do not depend on `AnnealedInput`. `TraceExpDerivatives.lean` supplies the derivative estimates used in the chaos proof. The logarithmic CLT uses the chaos remainder and the lower bound `Z ≥ 1`.

The sign-gauge module uses the shared `SYK.partitionFunction` directly. Parity for `Setting.Z`, vanishing first chaos, and the exact second-chaos coefficient are proved for every real inverse temperature in Gaussian $L^2$, without `AnnealedInput`. `Preliminaries.lean`, `PartitionDerivatives.lean`, and `SecondChaos.lean` supply the symmetry, dominated differentiation, and coefficient identification.

The manuscript develops the partition-function CLT through an exact second-chaos decomposition and a direct Rademacher estimate for all higher chaoses. It also develops the transfer to the centered log-partition function.

The current manuscript's `thm: input` states the deterministic annealed-pressure limit at every fixed real inverse temperature and differentiability of the limiting function. Its statement contains neither an expected quenched-pressure limit nor an almost-sure assertion. He2026 supplies the positive-temperature input; Gaussian symmetry and the identity at zero extend it to real temperatures. The manuscript's and Lean's relative, standardized, and logarithmic CLTs all exclude zero inverse temperature.

`Setting.integral_log_Y_isBigO` proves the explicit `O(N^(-2a))` logarithmic mean-error bound. `StandardModel.lean` constructs the standard model family and applies all three conditional CLTs; these results are Lean-checked without `sorryAx`. The finite Gaussian lemmas are separated from model symmetry and asymptotic CLT inputs while preserving the public declarations and normalization. The proposition remains an explicit assumption. Its proof and the pointwise-to-locally-uniform step in `lem:convex-derivatives` are deferred. See [the editing plan](EDITING_PLAN.md) for specifications and acceptance criteria.

For individual proof files and their main declarations, see the [lemma index](ARCHITECTURE.md#補助-lean-ファイルの役割).

## Verification

Compile the complete manuscript from `refs/`:

```bash
latexmk -pdf CLT_SYK.tex
```

Each file under `refs/sections/` can also be compiled from that directory, for example:

```bash
latexmk -pdf introduction.tex
```

Standalone section builds inherit the shared preamble from `CLT_SYK.tex`. Cross-references and citations whose definitions lie in other subfiles remain unresolved in a standalone build; the complete manuscript build resolves them.

The conditional CLT is integrated into `Main.lean`. The current `GaussianIBP.lean` diagnostics include deprecated Mathlib names and linter warnings. See the [input verification](../WORK_HISTORY.md#clt-input-2026-10-04) and [manuscript audit](../WORK_HISTORY.md#clt-audit-2026-10-04) for the completed checks. After modifying a Lean file, check it from the shared workspace root:

```bash
lake env lean SYK/CLT/path/to/File.lean
```

Use `lake build` for changes affecting the full workspace. The LaTeX manuscript and Lean formalization have separate verification requirements; successful verification of one does not establish the correctness of the other.
