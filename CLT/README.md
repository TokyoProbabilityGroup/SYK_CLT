# High-Temperature SYK Central Limit Theorem

This directory contains the manuscript and Lean formalization work for the central limit theorem governing high-temperature fluctuations of the SYK partition function and free energy.

## Current contents

- `FiniteModel.lean`: abstract finite Majorana partition functions, trace bounds, and Gaussian moment and logarithm estimates, with inputs `Params` and `MajoranaSystem`.
- `Main.lean`: the unique asymptotic family API `Setting q`, the assumed proposition `AnnealedInput q S`, and the conditional CLT statements.
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

`Preliminaries` imports `Main` for `Setting`, `Z`, and `Y`. The general Gaussian Hermite integration-by-parts API used by the active CLT modules is in `Probability/GaussianConcentration/Smooth.lean`; search there before opening the large `GaussianIBP.lean`.

## Current status

`FiniteModel.lean` defines the normalized Gaussian partition function for general finite-dimensional matrix Majorana systems. `Main.lean` defines families of diverging even system sizes and the relative, standardized, and centered logarithmic fluctuations. The three CLT statements take `{q : ℕ} (S : Setting q) (hFE : AnnealedInput q S)`; evenness and `q ≥ 4` are fields of `S`, with no duplicate arguments. `partition_and_log_partition_clt` states both CLTs with one common radius for real `|β| < βq` and limiting variance `(q!/2) β² (ℓ_q'(β))²`; `partition_clt` and `log_partition_clt` extract the individual conclusions. Standardization excludes zero inverse temperature. The annealed proposition is assumed for `S`; constructing it is outside the conditional CLT proof.

The main CLT theorem still has an explicitly authorized `sorry` proof placeholder. The finite-model proofs now establish tracelessness, `Z ≥ 1`, `partition_moments`, positivity and expectation one of `Y`, square integrability, integrability of both logarithms, and equality of their centered versions. Specialization to the standard representation gives the manuscript trace normalization. All 30 public finite-model theorems were checked without `sorryAx` on 2026-09-26, independently of `AnnealedInput`. The individual Main module and the full `CLT` library build successfully. `TraceExpDerivatives.lean` supplies the first derivative estimate used in the exact second-chaos proof; W06 remains complete. The current logarithmic CLT argument does not require the earlier concentration-based proof.

The sign-gauge module now imports alongside `Main` and uses the shared `SYK.partitionFunction` directly. F02 now proves parity for `Setting.Z`, vanishing first chaos, and the exact second-chaos coefficient for every real inverse temperature in Gaussian $L^2$, without `AnnealedInput`. `Preliminaries.lean`, `PartitionDerivatives.lean`, and `SecondChaos.lean` supply the symmetry, dominated differentiation, and coefficient identification; see the [current task](EDITING_PLAN.md#ticket-integration) and the [integration record](../WORK_HISTORY.md#merge-f01-2026-09-27).

The manuscript develops the partition-function CLT through an exact second-chaos decomposition and a direct Rademacher estimate for all higher chaoses. It also develops the transfer to the centered log-partition function.

Theorem 1.1 cites an external almost-sure free-energy limit. Its source, normalization, and almost-sure quantifiers still require an audit; the manuscript does not currently provide an internal proof of that limit. Several statement-level and editorial issues are recorded in `EDITING_PLAN.md`.

### Supporting Lean modules

- `Lemmas/GaussianIBP.lean` proves Gaussian integration-by-parts formulas. It derives the one-dimensional identity using exponential tilting and dominated differentiation, then provides a finite-dimensional multi-index Hermite formula under finite differentiability and exponential-growth bounds. It also applies that formula to a pair of Hermite polynomials using their polynomial growth. Applying the general hypotheses to the SYK partition function is still separate work.
- `Lemmas/GaussianChaos.lean` matches the Hermite functions and Gaussian measures used by the integration-by-parts and sign-parity results. `Lemmas/GaussianHermiteOrthogonality.lean` proves exact Hermite pairings and finite orthogonal projection.
- `Lemmas/GaussianHermiteDensity.lean` puts finite-coordinate polynomials in the Hermite span and transfers polynomial density to Hermite density. `Lemmas/GaussianMomentDetermination.lean` supplies moment uniqueness under exponential integrability.
- `Lemmas/GaussianPolynomialDensity.lean` proves finite-product Gaussian polynomial density, unconditional Hermite completeness, and convergence of the Hermite coefficient and homogeneous-degree sums in $L^2$.
- `Lemmas/Rademacher.lean` models independent signs by a uniform average over Boolean sign vectors. It bounds the elementary-symmetric order-`q` sign chaos using Newton identities and a sub-Gaussian estimate, yielding an exponential third-moment bound for even `q ≥ 4`. The separate even-multi-index counting identity remains unformalized. This is an estimate for the higher-chaos argument, not the completed CLT proof.
- `Lemmas/ConvexDerivatives.lean` proves that locally uniform convergence of differentiable convex functions, together with differentiability and continuous derivative of the limit, gives uniform convergence of derivatives on compact subsets of the open domain. It does not establish the required local uniform convergence from pointwise convergence; that input remains part of the F06 work.
- `Lemmas/SingularValues.lean` develops singular-value and Schatten estimates in finite-dimensional inner-product spaces. `Lemmas/MatrixTraceExponential.lean` uses them for normalized trace and Schatten estimates. `Lemmas/TraceExpDerivatives.lean` bounds the iterated derivatives of the normalized trace exponential at Hermitian matrices. These files have no proof placeholders, and the first derivative bound is applied to the partition function in `PartitionDerivatives.lean`. The arbitrary-order application remains F04 work.

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

The supporting lemma files are present, but their presence does not mean the CLT proof is complete or that every helper is integrated into `Main.lean`. The current `GaussianIBP.lean` diagnostics include deprecated Mathlib names and linter warnings. See `EDITING_PLAN.md` for the exact integration and verification status. After modifying a Lean file, check it from the shared workspace root:

```bash
lake env lean SYK/CLT/path/to/File.lean
```

Use `lake build` for changes affecting the full workspace. The LaTeX manuscript and Lean formalization have separate verification requirements; successful verification of one does not establish the correctness of the other.
