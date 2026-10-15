# SYK

Research on the Sachdev–Ye–Kitaev (SYK) model from the perspective of probability theory.
This repository contains the [manuscript source](Paper/CLT_SYK.tex) and Lean 4 formalization of [A Central Limit Theorem for High-Temperature SYK Model (arXiv:2610.18440)](https://arxiv.org/abs/2610.18440).

Read the **[online Blueprint on GitHub Pages](https://TokyoProbabilityGroup.github.io/SYK_CLT/)** for the mathematical overview, theorem statements, and their connections to Lean declarations.

See the [Lean library guide](SYK/README.md) for the formalized results, their assumptions, and the main declarations.

## Requirements

- Git and [elan, Lean's toolchain manager](https://github.com/leanprover/elan#installation), with `lake` available on your command line.
- Lean 4.32.2, selected automatically by the committed `lean-toolchain` files.
- Mathlib 4.32.2, fetched by Lake at the revision in `lake-manifest.json`.
- Verso Blueprint v4.32.0, fetched only when building the Blueprint package.

The first build needs internet access to download the toolchain, dependencies, and mathlib cache. Follow [Lean's installation guide](https://lean-lang.org/install/) for your platform, including the native compiler tools needed to build executable dependencies. Python 3 is needed for local Blueprint previews; LaTeX is needed for PDF generation.

## Setup instructions

Clone the public repository and run Lake from its root:

```bash
git clone https://github.com/TokyoProbabilityGroup/SYK_CLT.git
cd SYK_CLT
lake exe cache get
lake build
```

This checks the complete mathematical library, including `SYK/MainAudit.lean`. Dependencies are stored in `SYK_CLT/.lake/packages/`, and generated files are ignored by Git. Open `SYK_CLT/` as the project folder in your Lean editor.

Keep both `lake-manifest.json` files when cloning or sharing a revision. They pin the dependency commits; `lake update` is for intentional dependency upgrades and is not part of the normal setup. When upgrading dependencies, keep the two packages' toolchains and shared dependency revisions consistent.

## Building and testing

Run these commands from the repository root:

```bash
lake build SYK
lake lean SYK/Main.lean
lake lean SYK/CLT/Main.lean
```

`lake build` and `lake build SYK` check mathematics only. `lake lean <file>` builds the imports of one file and checks it with the package's `leanOptions` (linters included), unlike `lake env lean`, which only sets up the environment. To build mathematics together with its documentation, use the separate [Blueprint commands](#blueprint) below.

After changing a Lean file, check it individually before the full library build.

See the [Lean library guide](SYK/README.md#verification) for theorem-statement and axiom checks.

## Blueprint

The **[online Blueprint](https://TokyoProbabilityGroup.github.io/SYK_CLT/)** presents the mathematical statements and proof structure with links to Lean declarations. See the [Blueprint source guide](Blueprint/README.md) for the chapters, document entry point, and connections to the manuscript and Lean library.

### Building locally

From the repository root:

```bash
cd Blueprint
lake exe cache get
lake build SYKBlueprint
lake exe vbp build
lake exe vbp check
```

`lake build SYKBlueprint` checks the complete mathematical library together with the document and generator modules. `lake exe vbp build` runs `SYKBlueprintMain.lean` to generate the site. `lake exe vbp check` checks the manifest, HTML cache, and internal references; mathematical agreement with the manuscript requires a separate review.

Generated HTML is stored in `Blueprint/_out/site/html-multi/` and is ignored by Git. All remaining commands in this Blueprint section run from `Blueprint/`. Use `cd ..` to return to the repository root afterward.

This directory has its own Lake configuration, manifest, and toolchain. It depends on the mathematical package through `path = ".."` and stores external dependencies in `Blueprint/.lake/packages/`. Building both packages uses separate dependency checkouts, including separate copies of mathlib.

### Local preview

To build and serve the site:

```bash
lake exe vbp build --serve
```

Open the preview URL printed in the terminal. The server uses port 8000 when available and otherwise selects an available port. To require port 8000, add `--port 8000`.

To serve previously generated HTML without rebuilding:

```bash
python3 -m http.server 8000 --bind 127.0.0.1 --directory _out/site/html-multi
```

Open [http://localhost:8000/](http://localhost:8000/). Both preview methods require Python 3 and restrict access to the local machine. Neither automatically rebuilds the documentation when source files change. Stop the server with Ctrl-C.

### Editing and checking

After changing a chapter or referenced Lean declarations, check the affected chapters and both entry modules with `lake lean`. For example, after editing the CLT chapter:

```bash
lake lean SYKBlueprint/CLT.lean
lake lean SYKBlueprint.lean
lake lean SYKBlueprintMain.lean
lake build SYKBlueprint
lake exe vbp build
lake exe vbp check
```

Review mathematical statements, assumptions, normalizations, and declaration references against the Lean sources and manuscript. Use the manuscript's LaTeX labels when referring to its results.

### PDF generation

For an optional PDF, with a compatible LuaLaTeX installation:

```bash
lake exe vbp build --pdf
```

### Continuous integration and Pages deployment

[Lean Action CI](.github/workflows/lean_action_ci.yml) checks the mathematical package from the repository root and the Blueprint package from `Blueprint/`. It runs on pushes to `main` that change Lean sources, Lake configuration, toolchains, or the workflow itself. It can also be run manually. Pull requests do not trigger this workflow.

The workflow generates the Blueprint, runs `vbp check`, and deploys `Blueprint/_out/site/html-multi/` to GitHub Pages when running on `main`. Markdown-only changes do not trigger it; use a manual run on `main` to redeploy when needed.

For a fork or a new deployment, select **GitHub Actions** under **Settings → Pages → Build and deployment → Source**. The `github-pages` environment must allow deployments from `main`; approve the deployment if that environment requires approval. The deployment job reports the published URL.

## Manuscript

The preprint is available as [arXiv:2610.18440](https://arxiv.org/abs/2610.18440). To compile the source, start at the repository root:

```bash
cd Paper
latexmk -pdf CLT_SYK.tex
```

The four files under `Paper/sections/` can also be compiled independently from the `Paper/` directory, for example with `latexmk -cd -pdf sections/introduction.tex`; `-cd` runs LaTeX in the section's directory so its relative preamble path resolves correctly. References defined in other sections may remain unresolved in standalone builds. The manuscript and Lean formalization have separate verification requirements.

The [LaTeX workflow](.github/workflows/latex_action_ci.yml) compiles the paper and uploads its PDF as a workflow artifact.

## Licensing and citation

All original Lean source files (`.lean`) throughout this repository, including `SYK/` and `Blueprint/`, are licensed under the [Apache License 2.0](LICENSE). This grant applies only to the Lean sources. Dependencies and third-party material retain their own licenses and attribution notices; other documents, manuscripts, bibliographies, figures, and PDFs are outside this grant.

The accompanying paper, including its LaTeX sources, bibliography, and PDF, is copyrighted by its authors, with all rights reserved, and is not covered by Apache-2.0. See [Paper/COPYRIGHT.md](Paper/COPYRIGHT.md). The preprint is distributed by arXiv under its [perpetual, non-exclusive distribution license](https://arxiv.org/licenses/nonexclusive-distrib/1.0/); that license does not grant reuse rights to GitHub users.

Please cite Yoshinori Kamijima, Shuta Nakajima, Ryoichiro Noda, and Kôhei Sasaya, *A Central Limit Theorem for High-Temperature SYK Model*, [arXiv:2610.18440](https://arxiv.org/abs/2610.18440) (2026). [CITATION.cff](CITATION.cff) records the preferred paper citation and identifies the formalization repository. When referring to the Lean formalization, also include the [repository URL](https://github.com/TokyoProbabilityGroup/SYK_CLT) and the commit used.

