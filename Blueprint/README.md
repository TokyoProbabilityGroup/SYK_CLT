# Blueprint source guide

This directory contains the source of the **[online Blueprint](https://TokyoProbabilityGroup.github.io/SYK_CLT/)**, which presents the mathematical statements and proof structure with links to Lean declarations. For the formalized results and their assumptions, see the [Lean library guide](../SYK/README.md).

## Source files

[SYKBlueprint.lean](SYKBlueprint.lean) assembles the chapters in [SYKBlueprint/](SYKBlueprint/) and adds the dependency graph and summary. [SYKBlueprintMain.lean](SYKBlueprintMain.lean) is the generator entry point. The package configuration is in [lakefile.toml](lakefile.toml). The chapters cite manuscript results by their LaTeX labels in [the manuscript source](../Paper/).

## Building locally

In addition to the [repository requirements](../README.md#requirements), the local preview needs Python 3 and the PDF needs LuaLaTeX. From the repository root:

```bash
cd Blueprint
lake exe cache get
lake build SYKBlueprint
lake exe vbp build
lake exe vbp check
```

`lake build SYKBlueprint` checks the complete mathematical library together with the document and generator modules. `lake exe vbp build` runs `SYKBlueprintMain.lean` and writes the site to `_out/site/html-multi/`, which is ignored by Git. `lake exe vbp check` checks the manifest, HTML cache, and internal references. All remaining commands run from `Blueprint/`.

This directory is a separate Lake package with its own configuration, manifest, and toolchain. It depends on the mathematical package through `path = ".."` and stores its own copy of the external dependencies, including mathlib, in `Blueprint/.lake/packages/`. When upgrading dependencies, update both packages so that they use the same toolchain and mathlib revision, and update the versions listed in the [repository requirements](../README.md#requirements).

Lean editors start a separate Lean server for files in `Blueprint/`, which uses this package's dependencies. Run `lake exe cache get` in this directory before opening these files; otherwise the editor may start building mathlib from source.

### Preview and PDF

```bash
lake exe vbp build --serve
lake exe vbp build --pdf
```

`--serve` rebuilds the site and serves it on the local machine at the URL printed in the terminal; add `--port 8000` to require that port. Stop the server with Ctrl-C. `--pdf` also writes `_out/site/pdf/main.pdf`.

### After editing

After changing a chapter or a referenced Lean declaration, check the affected chapter and both entry modules, then rebuild and check the site. For example, after editing the CLT chapter:

```bash
lake lean SYKBlueprint/CLT.lean
lake lean SYKBlueprint.lean
lake lean SYKBlueprintMain.lean
lake build SYKBlueprint
lake exe vbp build
lake exe vbp check
```

A successful build and check do not establish agreement with the manuscript. Review the statements, assumptions, normalizations, and declaration references against the Lean sources and the manuscript.
