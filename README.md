# SYK

Research on the Sachdev–Ye–Kitaev (SYK) model from the perspective of probability theory.
This repository contains the [manuscript source](Paper/CLT_SYK.tex) and Lean 4 formalization of [A Central Limit Theorem for High-Temperature SYK Model (arXiv:2610.18440)](https://arxiv.org/abs/2610.18440).

The formalization is conditional on the annealed free-energy input (`prop:annealed-free-energy`), which the paper proves using cited results and which is not formalized; see the [Lean library guide](SYK/README.md#annealed-input).

Read the **[online Blueprint on GitHub Pages](https://TokyoProbabilityGroup.github.io/SYK_CLT/)** for the mathematical overview, theorem statements, and their connections to Lean declarations.

See the [Lean library guide](SYK/README.md) for the formalized results, their assumptions, and the main declarations.

## Requirements

- Git and [elan, Lean's toolchain manager](https://github.com/leanprover/elan#installation), with `lake` available on your command line.
- Lean 4.32.2, selected automatically by the committed `lean-toolchain` files.
- Mathlib 4.32.2, fetched by Lake at the revision in `lake-manifest.json`.
- Verso Blueprint v4.32.0, fetched only when building the Blueprint package.

The first build needs internet access to download the toolchain, dependencies, and mathlib cache. Follow [Lean's installation guide](https://lean-lang.org/install/) for your platform, including the native compiler tools needed to build executable dependencies.

## Setup instructions

Clone the public repository and run Lake from its root:

```bash
git clone https://github.com/TokyoProbabilityGroup/SYK_CLT.git
cd SYK_CLT
lake exe cache get
lake build
```

`lake build` checks the complete mathematical library, including `SYK/MainAudit.lean`. Dependencies are stored in `.lake/packages/`, and generated files are ignored by Git. Open the repository root as the project folder in your Lean editor. Files in `Blueprint/` belong to a separate Lake package; see the [Blueprint source guide](Blueprint/README.md#building-locally) before opening them. To inspect the main theorem statements and their axioms, see the [verification guide](SYK/README.md#verification).

## Blueprint

The **[online Blueprint](https://TokyoProbabilityGroup.github.io/SYK_CLT/)** presents the mathematical statements and proof structure with links to Lean declarations. GitHub Actions rebuilds and publishes it from `main`. To build it locally, see the [Blueprint source guide](Blueprint/README.md).

## Manuscript

The preprint is available as [arXiv:2610.18440](https://arxiv.org/abs/2610.18440). To compile the source, start at the repository root:

```bash
cd Paper
latexmk -pdf CLT_SYK.tex
```

## Licensing and citation

Except for the paper in `Paper/`, everything in this repository, including the Lean sources, the Blueprint, the documentation, and the build and CI configuration, is licensed under the [Apache License 2.0](LICENSE). Dependencies fetched by Lake retain their own licenses.

The accompanying paper, including its LaTeX sources, bibliography, and PDF, is copyrighted by its authors, with all rights reserved, and is not covered by Apache-2.0. See [Paper/COPYRIGHT.md](Paper/COPYRIGHT.md).

Please cite Yoshinori Kamijima, Shuta Nakajima, Ryoichiro Noda, and Kôhei Sasaya, *A Central Limit Theorem for High-Temperature SYK Model*, [arXiv:2610.18440](https://arxiv.org/abs/2610.18440) (2026). [CITATION.cff](CITATION.cff) records the preferred paper citation and identifies the formalization repository. When referring to the Lean formalization, also include the [repository URL](https://github.com/TokyoProbabilityGroup/SYK_CLT) and the commit used.
