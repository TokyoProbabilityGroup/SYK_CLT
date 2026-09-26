# High-Temperature SYK Central Limit Theorem

This directory contains the manuscript and Lean formalization work for the central limit theorem governing high-temperature fluctuations of the SYK partition function and free energy.

## Current contents

- `refs/CLT_SYK.tex`: manuscript root containing the shared preamble, front matter, and references.
- `refs/sections/`: independently compilable top-level manuscript sections; together with the root file, these are the source of truth for the paper theorem statements.
- `refs/CLT_SYK.pdf`: compiled manuscript snapshot.
- `ARCHITECTURE.md`: internal proof-dependency and status documentation.
- `EDITING_PLAN.md`: internal manuscript-audit and formalization plan.
- `Lemmas/GaussianIBP.lean` and `Lemmas/Rademacher.lean`: Gaussian integration-by-parts and Rademacher-chaos results related to the CLT proof.
- `Lemmas/ConvexDerivatives.lean`: a convex-convergence theorem for derivatives, used as an input to the annealed-limit argument.
- `AGENTS.md`: topic-specific instructions for Codex.

The internal planning documents are written in Japanese for collaboration between the researcher and Codex. Public mathematical artifacts, including this README, the manuscript, and future Lean source files, are written in English.

## Current status

`Main.lean` defines the normalized Gaussian partition function for general finite-dimensional matrix Majorana systems, families of diverging even system sizes, and the relative, standardized, and centered logarithmic fluctuations. `partition_and_log_partition_clt` states both CLTs with one common radius for real `|β| < βq` and limiting variance `(q!/2) β² (ℓ_q'(β))²`; `partition_clt` and `log_partition_clt` extract the individual conclusions. Standardization excludes zero inverse temperature. The annealed limit identifies `ℓ_q`.

The main CLT theorem still has an explicitly authorized `sorry` proof placeholder. The finite-model proofs now establish tracelessness, `Z ≥ 1`, `partition_moments`, positivity and expectation one of `Y`, square integrability, integrability of both logarithms, and equality of their centered versions. Specialization to the standard representation gives the manuscript trace normalization. All 30 public finite-model theorems were checked without `sorryAx` on 2026-09-26, independently of `AnnealedInput`. The individual Main module and the full `CLT` library build successfully. The unused `Tool.lean` was removed after checking that no other Lean module or manuscript/Blueprint claim referenced its declarations; W06 is complete. The current logarithmic CLT argument does not require the earlier concentration-based proof.

The manuscript develops the partition-function CLT through an exact second-chaos decomposition and a direct Rademacher estimate for all higher chaoses. It also develops the transfer to the centered log-partition function.

Theorem 1.1 cites an external almost-sure free-energy limit. Its source, normalization, and almost-sure quantifiers still require an audit; the manuscript does not currently provide an internal proof of that limit. Several statement-level and editorial issues are recorded in `EDITING_PLAN.md`.

### Supporting Lean modules

- `Lemmas/GaussianIBP.lean` proves Gaussian integration-by-parts formulas. It derives the one-dimensional identity using exponential tilting and dominated differentiation, then provides a finite-dimensional multi-index Hermite formula under finite differentiability and exponential-growth bounds. Applying those hypotheses to the SYK partition function is still separate work.
- `Lemmas/Rademacher.lean` models independent signs by a uniform average over Boolean sign vectors. It bounds the elementary-symmetric order-`q` sign chaos using Newton identities and a sub-Gaussian estimate, yielding an exponential third-moment bound for even `q ≥ 4`. This is an estimate for the higher-chaos argument, not the completed CLT proof.
- `Lemmas/ConvexDerivatives.lean` proves that locally uniform convergence of differentiable convex functions, together with differentiability and continuous derivative of the limit, gives uniform convergence of derivatives on compact subsets of the open domain. It does not establish the required local uniform convergence from pointwise convergence; that input remains part of the F06 work.

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
