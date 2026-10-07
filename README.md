# SYK

Research on the Sachdev–Ye–Kitaev (SYK) model from the perspective of probability theory.

## Abstract

## Requirements

- Lean 4.32.2
- Mathlib 4.32.2

## Setup instructions

To avoid duplicating the disk space used by [mathlib](https://github.com/leanprover-community/mathlib4), clone this repository into a workspace directory and copy the configuration files from `SYK/workspace/` to the workspace root, alongside the cloned `SYK/` directory.
Specifically, please run the following commands:

```bash
cd <working directory>  # Replace <working directory> with a path of your choice.
git clone git@github.com:TokyoProbabilityGroup/SYK.git
cp SYK/workspace/lakefile.toml .
cp SYK/workspace/lake-manifest.json .
cp SYK/workspace/lean-toolchain .
lake exe cache get
```

This produces the following directory structure:

```
<working directory>/
├── SYK/
│   ├── .git/
│   ├── .github/
│   ├── Annealed_FE/
│   ├── Blueprint.lean
│   ├── BlueprintMain.lean
│   ├── Chapters/
│   ├── ...
│   ├── workspace/
│   ├── .gitignore
│   └── README.md
├── .lake/
│   ├── build/
│   ├── config/
│   └── packages/
├── lake-manifest.json
├── lakefile.toml
└── lean-toolchain
```

## Building and testing

To build the workspace's default targets, run:

```bash
cd <working directory>
lake build
```

`defaultTargets` in `lakefile.toml` selects the libraries built by `lake build`.
The mathematical topics have individual targets such as `Model`, `SuperConcentration`, and `CLT`; the `SYK` target checks shared foundations under `SYK/Probability/`, Blueprint, the chapters, and their dependencies. `Annealed_FE` and `Universality` remain excluded from `defaultTargets`, but the AnnealedFE chapter imports `Annealed_FE.main_result` transitively, including its existing proof placeholders. Build success does not establish completion of those proofs.
The main CLTs are Lean-checked conditional on `AnnealedInput`; constructing that input remains a separate task. A successful build alone does not establish that the formal statements match every claim in the manuscript.
There is no aggregate Lean import file: Lake manages the build targets directly.
All project-specific Lean sources remain inside the repository; only the shared Lake configuration, dependency manifest, and toolchain file are copied to the workspace root.
To build one library separately, run a command such as `lake build Model`.
After modifying a Lean source file, first check that file directly from the workspace root.
For example:

```bash
lake env lean SYK/Model/Definitions.lean
```

## Blueprint

Verso Blueprint is enabled with pinned dependencies. The default build includes the chapters; CI also generates the HTML site and checks its references. See [workspace configuration](workspace/README.md#restoring-verso).

The formalization blueprint is written in `Blueprint.lean` and `Chapters/`.
To generate the HTML site and validate its manifest, run from the workspace root:

```bash
lake lean SYK/BlueprintMain.lean -- --run SYK/BlueprintMain.lean --output SYK/_out/site
lake exe vbp check --site SYK/_out/site
```

Check the affected chapters, `Blueprint.lean`, and `BlueprintMain.lean` with Lean, and run both commands after changing `Blueprint.lean`, `BlueprintMain.lean`, a file under `Chapters/`, or a Lean declaration name referenced by the Blueprint.
`lake lean` builds the entry point's imports and runs the renderer directly. No shell script or separately compiled renderer executable is required.
`vbp check` verifies the consistency of the generated manifest, HTML cache, and internal references.

The generated site is written to `SYK/_out/site/html-multi/` and is excluded from Git.
To build a PDF as well, append `--pdf` to the renderer command above.
This requires `lualatex`, or a compatible engine, to be available on `PATH`.
To inspect the generated site locally, run:

```bash
# The installed vbp build --serve only discovers generators at the workspace root.
# Our generator is SYK/BlueprintMain.lean, so serve the generated site directly.
# The built-in vbp server also uses Python's HTTP server internally.
python3 -m http.server 8000 --bind 127.0.0.1 --directory SYK/_out/site/html-multi
```

Then open `http://localhost:8000/`. Serving the generated site requires Python 3.

## References

- [Spin glass by Lean](https://github.com/or4nge19/SpinGlass)
