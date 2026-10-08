# High-Temperature SYK Central Limit Theorem

This directory contains the Lean formalization work for the central limit theorem governing high-temperature fluctuations of the SYK partition function and free energy.

## Current contents

- `FiniteModel.lean`: abstract finite Majorana partition functions, trace bounds, and Gaussian moment and logarithm estimates, with inputs `Params` and `MajoranaSystem`.
- `Basic.lean`: the asymptotic family API `Setting q` and the assumed annealed input `AnnealedInput q S`. `Main.lean` states the conditional CLTs.
- `StandardModel.lean`: the standard family of sizes `q + 2 * n`, its trace normalization, and the three conditional CLTs.
- `Normalization.lean`: the finite standard-representation check `partitionFunction_standard`; this module is not imported by the abstract CLT proofs.
- `../../Paper/CLT_SYK.tex`: manuscript root containing the shared preamble, front matter, and references.
- `../../Paper/sections/`: independently compilable top-level manuscript sections; together with the root file, these are the source of truth for the paper theorem statements.
- `ARCHITECTURE.md`: current mathematical API, proof dependencies, and manuscript correspondence.
- `EDITING_PLAN.md`: remaining convex-convergence, external-input, and annealed-input tasks.
- `AGENTS.md`: topic-specific instructions for Codex.

The internal planning documents are written in Japanese for collaboration between the researcher and Codex. Public mathematical artifacts, including this README, the manuscript, and Lean source files, are written in English.

## Finding a lemma

From the shared workspace root, start with a declaration name and its callers: `rg -n 'NAME' SYK/SYK/CLT SYK/SYK/Probability SYK/SYK/Model SYK/SYK/Analysis`. For an unfamiliar file, search its `theorem`, `lemma`, `def`, and `namespace` lines before reading proofs. Each lemma module's opening docstring lists its role and main entry points.

The principal import paths are:

| Task | Modules to inspect in order |
| --- | --- |
| Gaussian Hermite coefficients and completeness | `GaussianHermiteBasic` → `GaussianChaos` → `GaussianHermiteOrthogonality` → `GaussianHermiteDensity` and `GaussianMomentDetermination` → `GaussianPolynomialDensity` |
| Singular values and matrix derivatives | `SingularValues` → `MatrixTraceExponential` → `TraceExpDerivatives` |
| Finite SYK second chaos | `Basic`, `CliffordSignParity`, `GaussianHermiteOrthogonality` → `PartitionSymmetry`; `TraceExpDerivatives` → `PartitionDerivatives`; both → `SecondChaos` |
| Independent estimates | `Rademacher` or `ConvexDerivatives` |
| Quadratic Gaussian moments and CLT | `GaussianQuadraticObservable` → `GaussianFourthMoment` → `IndependentFourthMoment`; `GaussianQuadraticObservable` and `SecondChaosAsymptotic` → `GaussianQuadraticCLT` |

`PartitionSymmetry` imports `Basic` for `Setting`, `Z`, and `Y`. The general Gaussian Hermite integration-by-parts API used by the active CLT modules is in `../Probability/GaussianConcentration/Smooth.lean`; search there before opening the large `GaussianIBP.lean`. The latter retains the earlier scalar Stein integration-by-parts development and is outside the recursive imports of `Main`. It is still imported by the Blueprint chapter source and built by the complete `SYK` library glob.

`GaussianHermiteBasic` contains the finite product Gaussian measure, Hermite products, and their sign/permutation identities. `GaussianChaos` uses these without importing the model-specific `CliffordSignParity`. Finite quadratic observables and their first two moments are in `GaussianQuadraticObservable`; fourth-moment estimates do not import the quadratic CLT.

The [lemma index](ARCHITECTURE.md#補助-lean-ファイルの役割) gives the main declarations and assumptions. `MatrixTraceExponential` also documents the roles of its Duhamel, Schatten, word, and Taylor-coefficient estimates.

## Current status

For fixed even $q \ge 4$, conditional on `hFE : AnnealedInput q S`, the theorems supply a common radius $\beta_q>0$ for real inverse temperatures $0<|\beta|<\beta_q$. The relative fluctuations $N^{q/2-1}(Z_N/\mathbb E Z_N-1)$ and centered logarithmic fluctuations $N^{q/2-1}(\log Z_N-\mathbb E\log Z_N)$ converge in distribution to centered Gaussians with variance $(q!/2)\beta^2(\ell_q'(\beta))^2$. Here $\ell_q$ is the limit supplied by `hFE`; the standardized partition-function fluctuations converge to a centered Gaussian with variance $1$.

These conditional results in `Main.lean` are Lean-checked. `StandardModel.lean` applies them to the standard family `N=q+2*n`. The finite-model and Gaussian-chaos results, and the explicit logarithmic mean-error estimate, are also implemented. The annealed proposition and construction of `hFE` remain open.

See [the architecture document](ARCHITECTURE.md#現行原稿の主張) for the theorem statements, normalization, manuscript correspondence, proof dependencies, and formalization boundaries. The [editing plan](EDITING_PLAN.md) contains the three remaining tasks, and [the work history](../../WORK_HISTORY.md) records completed verification. Gaussian integration by parts and moment calculations are distinct from assuming the annealed limit.

## Verification

Compile the complete manuscript from `../../Paper/`:

```bash
latexmk -pdf CLT_SYK.tex
```

Each file under `../../Paper/sections/` can also be compiled from that directory, for example:

```bash
latexmk -pdf introduction.tex
```

Standalone section builds inherit the shared preamble from `CLT_SYK.tex`. Cross-references and citations whose definitions lie in other subfiles remain unresolved in a standalone build; the complete manuscript build resolves them.

The conditional CLT is integrated into `Main.lean`. The current `GaussianIBP.lean` diagnostics include deprecated Mathlib names and linter warnings. See the [input verification](../../WORK_HISTORY.md#clt-input-2026-10-04) and [manuscript audit](../../WORK_HISTORY.md#clt-audit-2026-10-04) for the completed checks. After modifying a Lean file, check it from the shared workspace root:

```bash
lake env lean SYK/SYK/CLT/path/to/File.lean
```

Use `lake build SYK` for the mathematical library and `lake build` for the complete workspace. Inspect the principal theorem types and `#print axioms` as described in [the repository guide](../../README.md#building-and-testing). The LaTeX manuscript and Lean formalization have separate verification requirements; successful verification of one does not establish the correctness of the other.
