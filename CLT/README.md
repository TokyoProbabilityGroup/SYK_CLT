# High-Temperature SYK Central Limit Theorem

This directory contains the manuscript and Lean formalization work for the central limit theorem governing high-temperature fluctuations of the SYK partition function and free energy.

## Current contents

- `refs/CLT_SYK.tex`: manuscript root containing the shared preamble, front matter, and references.
- `refs/sections/`: independently compilable top-level manuscript sections; together with the root file, these are the source of truth for the paper theorem statements.
- `refs/CLT_SYK.pdf`: compiled manuscript snapshot.
- `ARCHITECTURE.md`: internal proof-dependency and status documentation.
- `EDITING_PLAN.md`: internal manuscript-audit and formalization plan.
- `Lemmas/GaussianIBP.lean`, `Lemmas/Rademacher.lean`, and `Lemmas/Tool.lean`: reusable Gaussian, Rademacher-chaos, and matrix-analysis results related to the CLT proof.
- `Lemmas/ConvexDerivatives.lean`: a convex-convergence theorem for derivatives, used as an input to the annealed-limit argument.
- `AGENTS.md`: topic-specific instructions for Codex.

The internal planning documents are written in Japanese for collaboration between the researcher and Codex. Public mathematical artifacts, including this README, the manuscript, and future Lean source files, are written in English.

## Current status

`Main.lean` defines the normalized Gaussian partition function for general finite-dimensional matrix Majorana systems, families of diverging even system sizes, and the relative, standardized, and centered logarithmic fluctuations. `partition_and_log_partition_clt` states both CLTs with one common radius for real `|β| < βq` and limiting variance `(q!/2) β² (ℓ_q'(β))²`; `partition_clt` and `log_partition_clt` extract the individual conclusions. Standardization excludes zero inverse temperature. The annealed limit identifies `ℓ_q`.

The main CLT theorem still has an explicitly authorized `sorry` proof placeholder. The finite-model definition and several supporting statements have checked proofs, while `partition_moments` remains unfinished. The current logarithmic CLT argument does not require the earlier concentration-based proof.

The manuscript develops the partition-function CLT through an exact second-chaos decomposition and a direct Rademacher estimate for all higher chaoses. It also develops the transfer to the centered log-partition function.

Theorem 1.1 cites an external almost-sure free-energy limit. Its source, normalization, and almost-sure quantifiers still require an audit; the manuscript does not currently provide an internal proof of that limit. Several statement-level and editorial issues are recorded in `EDITING_PLAN.md`.

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

The supporting lemma files are present, but their presence does not mean the CLT proof is complete or that every helper is integrated into `Main.lean`. `Tool.lean` imports `RequestProject.*` modules whose sources are not present in this repository, and the current `GaussianIBP.lean` diagnostics include deprecated Mathlib names. See `EDITING_PLAN.md` for the exact integration and verification status. After modifying a Lean file, check it from the shared workspace root:

```bash
lake env lean SYK/CLT/path/to/File.lean
```

Use `lake build` for changes affecting the full workspace. The LaTeX manuscript and Lean formalization have separate verification requirements; successful verification of one does not establish the correctness of the other.
