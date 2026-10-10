# High-Temperature SYK Central Limit Theorem

This directory contains the Lean formalization work for the central limit theorem governing high-temperature fluctuations of the SYK partition function and free energy.

## Current contents

- `FiniteModel.lean`: abstract finite Majorana partition functions, trace bounds, and Gaussian moment and logarithm estimates, with inputs `Params` and `MajoranaSystem`.
- `Basic.lean`: the asymptotic family API `Setting q` and the assumed annealed input `AnnealedInput q S`. `Main.lean` states the conditional CLTs.
- `StandardModel.lean`: the standard family of sizes `q + 2 * n`, its trace normalization, and the three conditional CLTs.
- `Normalization.lean`: the finite standard-representation check `partitionFunction_standard`; this module is not imported by the abstract CLT proofs.
- `../../Paper/CLT_SYK.tex`: manuscript root containing the shared preamble, front matter, and references.
- `../../Paper/sections/`: independently compilable top-level manuscript sections; together with the root file, these are the source of truth for the paper theorem statements.
- `ARCHITECTURE.md` (Japanese): current mathematical API, proof dependencies, and manuscript correspondence.
- `EDITING_PLAN.md` (Japanese): current task status and the scope of the conditional CLT.
- `AGENTS.md` (Japanese): topic-specific instructions for coding agents.

The internal planning documents are written in Japanese for collaboration between the researcher and coding agents. Public mathematical artifacts, including this README, the manuscript, and Lean source files, are written in English.

## Finding a lemma

From the shared workspace root, start with a declaration name and its callers: `rg -n 'NAME' SYK_CLT/SYK/CLT SYK_CLT/SYK/Probability SYK_CLT/SYK/Model SYK_CLT/SYK/Analysis`. For an unfamiliar file, search its `theorem`, `lemma`, `def`, and `namespace` lines before reading proofs. Each lemma module's opening docstring lists its role and main entry points.

The principal import paths are:

| Task | Modules to inspect in order |
| --- | --- |
| Gaussian Hermite coefficients and completeness | `GaussianChaos/Basic` → `GaussianChaos/CoefficientIBP` → `GaussianChaos/Orthogonality` → `GaussianChaos/HermiteDensity` and `GaussianMomentDetermination` → `GaussianChaos/PolynomialDensity` |
| Singular values and matrix derivatives | `SingularValues` → `TraceExponential` → `TraceExpDerivatives` |
| Finite SYK second chaos | `Basic`, `CliffordSignParity`, `GaussianChaos/Orthogonality` → `PartitionSymmetry`; `TraceExpDerivatives` → `PartitionDerivatives`; both → `SecondChaos` |
| Independent estimates | `Rademacher` or `ConvexDerivatives` |
| Quadratic Gaussian moments and CLT | `GaussianQuadraticObservable` → `GaussianFourthMoment` → `IndependentFourthMoment`; `GaussianQuadraticObservable` and `SecondChaosAsymptotic` → `GaussianQuadraticCLT` |

`PartitionSymmetry` imports `Basic` for `Setting`, `Z`, and `Y`. The general Gaussian Hermite integration-by-parts API used by the active CLT modules is in `../Probability/GaussianConcentration/HermiteIBP.lean`.

`GaussianChaos/Basic` contains the finite product Gaussian measure, Hermite products, and their sign/permutation identities. `GaussianChaos/CoefficientIBP` uses these without importing the model-specific `CliffordSignParity`. Finite quadratic observables and their first two moments are in `GaussianQuadraticObservable`; fourth-moment estimates do not import the quadratic CLT.

The opening docstring of each module also states its main declarations and assumptions; `TraceExponential`, for example, documents the roles of its Schatten, word, and Taylor-coefficient estimates.

## Current status

For fixed even $q \ge 4$, conditional on `hFE : AnnealedInput q S`, the theorems supply a common radius $\beta_q>0$ for real inverse temperatures $0<|\beta|<\beta_q$. The relative fluctuations $N^{q/2-1}(Z_N/\mathbb E Z_N-1)$ and centered logarithmic fluctuations $N^{q/2-1}(\log Z_N-\mathbb E\log Z_N)$ converge in distribution to centered Gaussians with variance $(q!/2)\beta^2(\ell_q'(\beta))^2$. Here $\ell_q$ is the limit supplied by `hFE`; the standardized partition-function fluctuations converge to a centered Gaussian with variance $1$.

These conditional results in `Main.lean` are Lean-checked. `StandardModel.lean` applies them to the standard family `N=q+2*n`. The finite-model and Gaussian-chaos results, and the explicit logarithmic mean-error estimate, are also implemented. The annealed proposition and construction of `hFE` remain unformalized and are outside the agreed formalization scope.

The theorem statements are in `Main.lean` for an abstract family and in `StandardModel.lean` for the standard family; `AnnealedInput` is declared in `Basic.lean`. The CLT chapter of the [Blueprint](../../Blueprint/SYKBlueprint/CLT.lean) explains the statements, normalization, and the boundary between formalized and assumed parts. Gaussian integration by parts and moment calculations are distinct from assuming the annealed limit.

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

The conditional CLT is integrated into `Main.lean`. For `partition_clt`, `log_partition_clt`, `partition_and_log_partition_clt` and the three standard-family theorems in `StandardModel.lean`, `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`; `hFE : AnnealedInput q S` remains an explicit hypothesis. After modifying a Lean file, check it from the shared workspace root:

```bash
lake lean SYK_CLT/SYK/CLT/path/to/File.lean
```

Use `lake build SYK` for the mathematical library and `lake build SYKBlueprint` for the mathematics together with the Blueprint. Inspect the principal theorem types and `#print axioms` as described in [the repository guide](../../README.md#building-and-testing). The LaTeX manuscript and Lean formalization have separate verification requirements; successful verification of one does not establish the correctness of the other.
