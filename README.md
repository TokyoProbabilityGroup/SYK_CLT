# SYK

Research on Sachdev–Ye–Kitaev (SYK) model from a point of view of Probability Theory.

## Abstract

## Requirements

- Lean 4.32.2
- Mathlib 4.32.2

## Setup instructions

To save storage space mostly used by [mathlib](https://github.com/leanprover-community/mathlib4), we recommend that you should clone this repository into a working directory and copy configuration files in `SYK/workspace` into the same level as the cloned repository.
Specifically, please run the following commands:

```bash
cd <working directory>  # Replace the working directory name with that you prefer.
git clone git@github.com:TokyoProbabilityGroup/SYK.git
cp SYK/workspace/lakefile.toml .
cp SYK/workspace/lake-manifest.json .
cp SYK/workspace/lean-toolchain .
lake exe cache get
```

Then, we arrive at the directory structure

```
<working directory>/
├── SYK/
│   ├── .git/
│   ├── .github/
│   ├── Annealed_FE/
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
└── lean-toolchain
```

## Minimal Usage

To build all libraries, run

```bash
cd <working directory>
lake exe mk_all
lake build
```

The command `lake exe mk_all` generates a Lean source file on which the `import` statement is written.
It is required to build all math libraries as the default target (See also the `lakefile.toml` file).
When you would like to build each library individually, for example, you should just run `lake build SYK_model`.
