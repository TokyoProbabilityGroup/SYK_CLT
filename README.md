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
cp SYK/workspace/SYK.lean .
cp SYK/workspace/SYKMain.lean .
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
│   ├── Chapters/
│   ├── ...
│   ├── Universality/
│   ├── workspace/
│   ├── .gitignore
│   └── README.md
├── .lake/
│   ├── build/
│   ├── config/
│   └── packages/
├── lake-manifest.json
├── lakefile.toml
├── lean-toolchain
├── SYK.lean
└── SYKMain.lean
```

## Building and testing

To build all libraries, run:

```bash
cd <working directory>
lake build
```

The version-controlled template `workspace/SYK.lean` imports the project modules used by the default target.
To build one library separately, run a command such as `lake build Model`.
After modifying a Lean source file, first check that file directly from the workspace root.
For example:

```bash
lake env lean SYK/Model/Definitions.lean
```

## Blueprint

The formalization blueprint is written in `Blueprint.lean` and `Chapters/`.
To generate the HTML site and validate its manifest, run from the workspace root:

```bash
lake exe vbp build
lake exe vbp check
```

Run both commands after changing `Blueprint.lean`, a file under `Chapters/`, or a Lean declaration name referenced by the Blueprint.
The build command generates the site, and `vbp check` verifies the consistency of the generated manifest, HTML cache, and internal references.

The generated site is written to `_out/site/html-multi/`.
To build a PDF as well, run `lake exe vbp build --pdf`.
This requires `lualatex`, or a compatible engine, to be available on `PATH`.
To inspect the generated site locally, run:

```bash
lake exe vbp build --serve
```

## References

- [Spin glass by Lean](https://github.com/or4nge19/SpinGlass)
