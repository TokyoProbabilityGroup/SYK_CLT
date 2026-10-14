# SYK

Research on the Sachdev–Ye–Kitaev (SYK) model from the perspective of probability theory.
This repository contains the [manuscript source](Paper/CLT_SYK.tex) and Lean 4 formalization of [A Central Limit Theorem for High-Temperature SYK Model (arXiv:2610.18440)](https://arxiv.org/abs/2610.18440), with the remaining assumptions described below.

Read the **[online Blueprint on GitHub Pages](https://TokyoProbabilityGroup.github.io/SYK_CLT/)** for the mathematical overview, theorem statements, and their connections to Lean declarations.

## Requirements

- Git and [elan, Lean's toolchain manager](https://github.com/leanprover/elan#installation), with `lake` available on your command line.
- Lean 4.32.2, selected automatically by the committed `lean-toolchain` files.
- Mathlib 4.32.2, fetched by Lake at the revision in `lake-manifest.json`.
- Verso Blueprint v4.32.0, fetched only when building the Blueprint package.

The first build needs internet access to download the toolchain, dependencies, and mathlib cache. Follow [Lean's installation guide](https://lean-lang.org/install/) for your platform, including the native compiler tools needed to build executable dependencies. Python 3 is needed only for the local HTTP server below; LaTeX is needed only for PDF generation.

## Repository layout

```text
SYK_CLT/                   # repository and mathematical Lake package
├── SYK/                   # mathematical Lean modules, namespace SYK
│   ├── Main.lean          # standalone Gaussian SYK model and public CLTs
│   ├── MainAudit.lean     # build-time check of standalone statements
│   ├── Analysis/
│   ├── Probability/
│   ├── Model/
│   ├── SuperConcentration/
│   └── CLT/               # Chaos, Quadratic, Limit, Log, and main results
├── Paper/                 # CLT_SYK.tex and its four sections
├── Blueprint/             # SYKBlueprint package: document, generator entry point, four chapters
├── lakefile.toml           # mathlib-only mathematical package
├── lake-manifest.json      # pinned mathematical dependencies
└── lean-toolchain          # Lean version
```

The CLTs assume the Gaussian `AnnealedInput` explicitly. See the [CLT guide](SYK/CLT/README.md) and the [concentration guide](SYK/SuperConcentration/README.md) for the current statements and verification commands.

## Setup instructions

Clone the public repository and run Lake from its root:

```bash
git clone https://github.com/TokyoProbabilityGroup/SYK_CLT.git
cd SYK_CLT
lake exe cache get
lake build
```

This checks the complete mathematical library, including `SYK/MainAudit.lean`. The repository is self-contained: no Lake configuration or dependency cache is required in its parent directory. Dependencies are stored in `SYK_CLT/.lake/packages/`, and generated files are ignored by Git. Open `SYK_CLT/` as the project folder in your Lean editor.

Keep both `lake-manifest.json` files when cloning or sharing a revision. They pin the dependency commits; `lake update` is for intentional dependency upgrades and is not part of the normal setup. When upgrading dependencies, keep the two packages' toolchains and shared dependency revisions consistent.

## Building and testing

Run these commands from the repository root:

```bash
lake build SYK
lake lean SYK/Main.lean
lake lean SYK/CLT/Main.lean
```

`lake build` and `lake build SYK` check mathematics only. `lake lean <file>` builds the imports of one file and checks it with the package's `leanOptions` (linters included), unlike `lake env lean`, which only sets up the environment. To build mathematics together with its documentation, use the separate [Blueprint commands](#blueprint) below.

The CLTs are Lean-checked conditional on `AnnealedInput`; constructing that input remains separate. Build success alone does not establish agreement between the formal statements and every manuscript claim. After changing a Lean file, check it individually before the full library build.

For the main results, inspect their types and axiom dependencies in a Lean editor or scratch file at the repository root:

```lean
import SYK.Main
import SYK.CLT.StandardModel

#check SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt
#print axioms SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt
#check SYK.CLT.partition_and_log_partition_clt
#print axioms SYK.CLT.partition_and_log_partition_clt
#check SYK.CLT.standard_partition_and_log_partition_clt
#print axioms SYK.CLT.standard_partition_and_log_partition_clt
```

Check the displayed assumptions, quantifier order, normalizations, and conclusions against the manuscript. All these theorems require an explicit `hFE : AnnealedInput ...`; `#print axioms` checks their axiom dependencies but does not prove this input. These statement and assumption checks are needed when assessing which manuscript claims the formalization verifies, in addition to routine builds.

## Blueprint

The published site is **[https://TokyoProbabilityGroup.github.io/SYK_CLT/](https://TokyoProbabilityGroup.github.io/SYK_CLT/)**. To generate it locally, start at the repository root:

```bash
cd Blueprint
lake exe cache get
lake build SYKBlueprint
lake exe vbp build
lake exe vbp check --site _out/site
```

`Blueprint/` has its own Lake configuration, manifest, and toolchain. It uses the mathematical package through `path = ".."` and stores its external dependencies in `Blueprint/.lake/packages/`. Building both packages therefore uses separate dependency checkouts, including separate copies of mathlib. `lake build SYKBlueprint` checks the full mathematical library as well as the document and generator modules.

`lake exe vbp build` discovers `SYKBlueprintMain.lean` in the current directory and runs it through Lake, which loads the native dependencies required by the renderer. The generator also retains its Windows search-asset handling. After changing documentation or referenced declarations, check the affected chapters and both entry modules with `lake lean`, then regenerate and check the site. `vbp check` verifies manifest, HTML cache, and internal-reference consistency; it does not prove mathematical claims.

Generated HTML is under `Blueprint/_out/site/html-multi/` and is ignored by Git. For an optional PDF, run `lake exe vbp build --pdf` from `Blueprint/`; a compatible LuaLaTeX environment is required. To serve the generated HTML, remain in `Blueprint/` and run:

```bash
python3 -m http.server 8000 --bind 127.0.0.1 --directory _out/site/html-multi
```

Open [http://localhost:8000/](http://localhost:8000/). Stop the server with Ctrl-C, then use `cd ..` to return to the repository root.

### Continuous integration and Pages deployment

[Lean Action CI](.github/workflows/lean_action_ci.yml) checks the mathematical package from the repository root and the documentation package from `Blueprint/`. Changes to Lean sources, Lake configuration, toolchains, or that workflow trigger checks on pushes to `main` and pull requests targeting `main`. The workflow can also be run manually. It generates the Blueprint and runs `vbp check` before uploading `Blueprint/_out/site/html-multi/` for Pages deployment. Only runs on `main` outside pull requests deploy; other runs only build and check.

For a fork or a new deployment, select **GitHub Actions** under **Settings → Pages → Build and deployment → Source**. The `github-pages` environment must allow deployments from `main`; approve the deployment if that environment requires approval. The deployment job reports the published URL. Markdown-only changes do not regenerate the site; a manual run on `main` can redeploy it. The separate [LaTeX Action CI](.github/workflows/latex_action_ci.yml) compiles the paper and uploads the PDF as a workflow artifact.

### Migrating from the former shared workspace

Run mathematics commands from `SYK_CLT/` and Blueprint commands from `SYK_CLT/Blueprint/`. The old `workspace/` template is no longer distributed. Parent-level `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` files created solely for the former `ResearchWorkspace` can be removed; preserve them if another project still uses them. The parent `.lake/` cache is no longer used by this repository. Run `lake exe cache get` separately in each package you intend to build. Existing generated files under `SYK_CLT/_out/site/` belong to the old layout; new Blueprint output is under `SYK_CLT/Blueprint/_out/site/`.

## Manuscript

The preprint is available as [arXiv:2610.18440](https://arxiv.org/abs/2610.18440). To compile the source, start at the repository root:

```bash
cd Paper
latexmk -pdf CLT_SYK.tex
```

The four files under `Paper/sections/` can also be compiled independently from the `Paper/` directory, for example with `latexmk -cd -pdf sections/introduction.tex`; `-cd` runs LaTeX in the section's directory so its relative preamble path resolves correctly. References defined in other sections may remain unresolved in standalone builds. The manuscript and Lean formalization have separate verification requirements.

## Licensing and citation

All original Lean source files (`.lean`) throughout this repository, including `SYK/` and `Blueprint/`, are licensed under the [Apache License 2.0](LICENSE). This grant applies only to the Lean sources. Dependencies and third-party material retain their own licenses and attribution notices; other documents, manuscripts, bibliographies, figures, and PDFs are outside this grant.

The accompanying paper, including its LaTeX sources, bibliography, and PDF, is copyrighted by its authors, with all rights reserved, and is not covered by Apache-2.0. See [Paper/COPYRIGHT.md](Paper/COPYRIGHT.md). The preprint is distributed by arXiv under its [perpetual, non-exclusive distribution license](https://arxiv.org/licenses/nonexclusive-distrib/1.0/); that license does not grant reuse rights to GitHub users.

Please cite Yoshinori Kamijima, Shuta Nakajima, Ryoichiro Noda, and Kôhei Sasaya, *A Central Limit Theorem for High-Temperature SYK Model*, [arXiv:2610.18440](https://arxiv.org/abs/2610.18440) (2026). [CITATION.cff](CITATION.cff) records the preferred paper citation and identifies the formalization repository. When referring to the Lean formalization, also include the [repository URL](https://github.com/TokyoProbabilityGroup/SYK_CLT) and the commit used.

