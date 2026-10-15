# Blueprint source guide

Read the **[online Blueprint](https://TokyoProbabilityGroup.github.io/SYK_CLT/)** for the mathematical overview, theorem statements, and their connections to Lean declarations. Building, reference checks, local previews, PDF generation, and Pages deployment are described in the [repository guide](../README.md#blueprint).

## Chapters

The document presents four chapters in the following order:

| Chapter | Contents |
| --- | --- |
| [Model](SYKBlueprint/Model.lean) | Finite-dimensional SYK model, Majorana operators, and normalization conventions |
| [Gaussian concentration](SYKBlueprint/GaussianConcentration.lean) | Gaussian concentration estimates used by the SYK application |
| [Superconcentration](SYKBlueprint/SuperConcentration.lean) | Majorana bounds and concentration of the SYK log-partition function |
| [Central limit theorem](SYKBlueprint/CLT.lean) | Chaos estimates, partition and log-partition CLTs, and the assumed annealed input |

## Document and generator

[SYKBlueprint.lean](SYKBlueprint.lean) assembles the chapters and adds the dependency graph and summary. [SYKBlueprintMain.lean](SYKBlueprintMain.lean) is the generator entry point. The package configuration is in [lakefile.toml](lakefile.toml).

## Reading the formalization

The chapters connect mathematical statements and proof dependencies to declarations in the Lean library. For the public theorem names and an overview of the mathematical modules, see the [Lean library guide](../SYK/README.md).

The CLTs are conditional on `AnnealedInput`; construction of this input remains outside the formalization scope. The Gaussian concentration results do not depend on it. Distinguish these explicit hypotheses from the axiom dependencies of the proofs.

The [manuscript](../Paper/CLT_SYK.tex) and its [sections](../Paper/sections/) record the paper's statements and arguments. References to manuscript results use their LaTeX labels. When comparing a Blueprint statement with the manuscript and Lean declaration, check the assumptions, quantifiers, normalizations, and conclusions; successful site generation and reference checks alone do not establish mathematical agreement.
