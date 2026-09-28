# High-Temperature SYK Central Limit Theorem

This directory contains the manuscript and Lean formalization work for the central limit theorem governing high-temperature fluctuations of the SYK partition function and free energy.

## Current contents

- `FiniteModel.lean`: abstract finite Majorana partition functions, trace bounds, and Gaussian moment and logarithm estimates, with inputs `Params` and `MajoranaSystem`.
- `Basic.lean`: the asymptotic family API `Setting q` and the assumed proposition `AnnealedInput q S`. `Main.lean` states the conditional CLTs.
- `Normalization.lean`: the finite standard-representation check `partitionFunction_standard`; this module is not imported by the abstract CLT proofs.
- `refs/CLT_SYK.tex`: manuscript root containing the shared preamble, front matter, and references.
- `refs/sections/`: independently compilable top-level manuscript sections; together with the root file, these are the source of truth for the paper theorem statements.
- `refs/CLT_SYK.pdf`: compiled manuscript snapshot.
- `ARCHITECTURE.md`: internal proof-dependency and status documentation.
- `EDITING_PLAN.md`: internal manuscript-audit and formalization plan.
- `Lemmas/GaussianIBP.lean`, `Lemmas/GaussianChaos.lean`, `Lemmas/GaussianHermiteOrthogonality.lean`, `Lemmas/GaussianHermiteDensity.lean`, `Lemmas/GaussianMomentDetermination.lean`, `Lemmas/GaussianPolynomialDensity.lean`, and `Lemmas/Rademacher.lean`: Gaussian integration by parts, Hermite coefficient and projection facts, polynomial spanning and analytic density inputs, and Rademacher-chaos results related to the CLT proof.
- `Lemmas/CliffordSignParity.lean`: sign-gauge and Hermite-parity results using the shared partition function.
- `Lemmas/ConvexDerivatives.lean`: a convex-convergence theorem for derivatives, used as an input to the annealed-limit argument.
- `Lemmas/SingularValues.lean`: finite-dimensional singular-value and Schatten-norm infrastructure. `Lemmas/MatrixTraceExponential.lean` uses it for normalized trace and exponential estimates; `Lemmas/TraceExpDerivatives.lean` proves the derivative bounds.
- `AGENTS.md`: topic-specific instructions for Codex.

The internal planning documents are written in Japanese for collaboration between the researcher and Codex. Public mathematical artifacts, including this README, the manuscript, and future Lean source files, are written in English.

## Finding a lemma

Start with a declaration name and its callers: `rg -n 'NAME' CLT Probability Model`. For an unfamiliar file, search its `theorem`, `lemma`, `def`, and `namespace` lines before reading proofs. Each lemma module's opening docstring lists its role and main entry points.

The principal import paths are:

| Task | Modules to inspect in order |
| --- | --- |
| Gaussian Hermite coefficients and completeness | `GaussianChaos` → `GaussianHermiteOrthogonality` → `GaussianHermiteDensity` and `GaussianMomentDetermination` → `GaussianPolynomialDensity` |
| Singular values and matrix derivatives | `SingularValues` → `MatrixTraceExponential` → `TraceExpDerivatives` |
| Finite SYK second chaos | `Main`, `CliffordSignParity`, `GaussianHermiteOrthogonality` → `Preliminaries`; `TraceExpDerivatives` → `PartitionDerivatives`; both → `SecondChaos` |
| Independent estimates | `Rademacher` or `ConvexDerivatives` |

`Preliminaries` imports `Basic` for `Setting`, `Z`, and `Y`. The general Gaussian Hermite integration-by-parts API used by the active CLT modules is in `Probability/GaussianConcentration/Smooth.lean`; search there before opening the large `GaussianIBP.lean`.

## Current status

`FiniteModel.lean` defines the normalized Gaussian partition function for general finite-dimensional matrix Majorana systems. `Basic.lean` defines families of diverging even system sizes, the relative, standardized, and centered logarithmic fluctuations, and `AnnealedInput`. The three CLT statements in `Main.lean` take `{q : ℕ} (S : Setting q) (hFE : AnnealedInput q S)`; evenness and `q ≥ 4` are fields of `S`, with no duplicate arguments. `partition_and_log_partition_clt` states all three CLTs with one common radius for real `0 < |β| < βq` and limiting variance `(q!/2) β² (ℓ_q'(β))²`; `partition_clt` and `log_partition_clt` extract the individual conclusions. The annealed proposition is assumed for `S`; constructing it is outside the conditional CLT proof.

The joint CLT and both individual CLTs are Lean-checked without `sorryAx`, conditional on `AnnealedInput`. The finite-model proofs establish tracelessness, `Z ≥ 1`, `partition_moments`, positivity and expectation one of `Y`, square integrability, integrability of both logarithms, and equality of their centered versions. Specialization to the standard representation gives the manuscript trace normalization. All 30 public finite-model theorems were checked without `sorryAx` on 2026-09-26, independently of `AnnealedInput`. `TraceExpDerivatives.lean` supplies the first derivative estimate used in the exact second-chaos proof; W06 remains complete. The logarithmic CLT uses the chaos remainder and the lower bound `Z ≥ 1`.

The sign-gauge module now imports alongside `Main` and uses the shared `SYK.partitionFunction` directly. F02 now proves parity for `Setting.Z`, vanishing first chaos, and the exact second-chaos coefficient for every real inverse temperature in Gaussian $L^2$, without `AnnealedInput`. `Preliminaries.lean`, `PartitionDerivatives.lean`, and `SecondChaos.lean` supply the symmetry, dominated differentiation, and coefficient identification; see the [current task](EDITING_PLAN.md#ticket-integration) and the [integration record](../WORK_HISTORY.md#merge-f01-2026-09-27).

The manuscript develops the partition-function CLT through an exact second-chaos decomposition and a direct Rademacher estimate for all higher chaoses. It also develops the transfer to the centered log-partition function.

The manuscript's `thm: input` states a deterministic common limit for expected quenched and annealed pressures, with no almost-sure assertion. Its positive-temperature source is He2026; Gaussian symmetry and the zero-temperature identity extend the statement to real inverse temperatures. The manuscript's and Lean's relative, standardized, and logarithmic CLTs all exclude zero inverse temperature. R01–R05 and F01–F08 are complete in the scoped sense recorded in `EDITING_PLAN.md`; `AnnealedInput` remains an assumed external input.

### Supporting Lean modules

- `Lemmas/GaussianIBP.lean` proves Gaussian integration-by-parts formulas. It derives the one-dimensional identity using exponential tilting and dominated differentiation, then provides a finite-dimensional multi-index Hermite formula under finite differentiability and exponential-growth bounds. It also applies that formula to a pair of Hermite polynomials using their polynomial growth. `PartitionHigherDerivatives.lean` verifies the hypotheses needed to apply it to the SYK partition function.
- `Lemmas/GaussianChaos.lean` matches the Hermite functions and Gaussian measures used by the integration-by-parts and sign-parity results. `Lemmas/GaussianHermiteOrthogonality.lean` proves exact Hermite pairings and finite orthogonal projection.
- `Lemmas/GaussianHermiteDensity.lean` puts finite-coordinate polynomials in the Hermite span and transfers polynomial density to Hermite density. `Lemmas/GaussianMomentDetermination.lean` supplies moment uniqueness under exponential integrability.
- `Lemmas/GaussianPolynomialDensity.lean` proves finite-product Gaussian polynomial density, unconditional Hermite completeness, and convergence of the Hermite coefficient and homogeneous-degree sums in $L^2$.
- `Lemmas/Rademacher.lean` models independent signs by a uniform average over Boolean sign vectors. Its factorial-weighted even-multi-index moment identity and exponential third-moment bound for even `q ≥ 4` are Lean-checked. `PartitionHigherDerivatives.lean` connects the all-order matrix derivative bound to `Setting.Z` and Gaussian Hermite integration by parts. `HigherChaosProjection.lean` bounds each homogeneous projection and their infinite sum, then proves the high-temperature `N^{-3(q/2-1)}` bound and `o(N^{2-q})`.
- `Lemmas/SecondChaosAsymptotic.lean` proves `choose N q ∼ N^q/q!` and combines it with `AnnealedInput` to obtain the exact limiting coefficient of the scaled second chaos. `Lemmas/GaussianQuadraticCLT.lean` proves the standard CLT for its independent quadratic Gaussian coordinates. `HigherChaosRemainder.lean` proves the exact $L^2$ tail identity and vanishing scaled remainder; `ZeroChaos.lean` separates the quadratic term from the remainder. `DistributionTransfer.lean` handles changing coefficients, and `LpDistributionTransfer.lean` transfers vanishing $L^2$ errors across varying probability spaces. `QuadraticBridge.lean` identifies the quadratic sum; `RelativeCLT.lean` proves its conditional CLT with the remainder; `EuclideanRelativeCLT.lean` transports that result to the model coupling measure and the exact `limitVariance`. `QuadraticGaussianVariance.lean` proves the exact quadratic-plus-remainder variance split and convergence of the normalized partition variance to `limitVariance`. `FiniteVariancePositivity.lean` proves positive disorder variance at every size for nonzero inverse temperature. `StandardizedCLT.lean` proves the standardized Gaussian limit. `partition_clt` is checked independently of the logarithmic transfer.
- `Lemmas/LogTaylor.lean` gives the pointwise quadratic error bound for `log Y`, its small-event upper bound, integrability, and the exact centered error identity. `GaussianFourthMoment.lean` and `IndependentFourthMoment.lean` prove a uniform fourth-moment bound for the normalized quadratic sum. `LogEventBound.lean` derives the finite-size small-event estimate; `LogAsymptotics.lean` proves the vanishing scaled tail, expected and centered logarithmic errors, and the logarithmic CLT.
- `Lemmas/ConvexDerivatives.lean` proves that locally uniform convergence of differentiable convex functions, together with differentiability and continuous derivative of the limit, gives uniform convergence of derivatives on compact subsets of the open domain. The required local uniform convergence is supplied by `AnnealedInput` for the conditional CLT.
- `Lemmas/SingularValues.lean` develops singular-value and Schatten estimates in finite-dimensional inner-product spaces. `Lemmas/MatrixTraceExponential.lean` uses them for normalized trace and exponential estimates, and `Lemmas/TraceExpDerivatives.lean` bounds all iterated derivatives at Hermitian matrices. `PartitionDerivatives.lean` applies the first derivative bound to the partition function; `PartitionHigherDerivatives.lean` applies the arbitrary-order bound.

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

The conditional CLT is integrated into `Main.lean`. The current `GaussianIBP.lean` diagnostics include deprecated Mathlib names and linter warnings. See `EDITING_PLAN.md` for the exact integration and verification status. After modifying a Lean file, check it from the shared workspace root:

```bash
lake env lean SYK/CLT/path/to/File.lean
```

Use `lake build` for changes affecting the full workspace. The LaTeX manuscript and Lean formalization have separate verification requirements; successful verification of one does not establish the correctness of the other.
