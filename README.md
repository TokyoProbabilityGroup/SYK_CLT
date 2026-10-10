# SYK

Research on the Sachdev–Ye–Kitaev (SYK) model from the perspective of probability theory.

## Requirements

- Lean 4.32.2
- Mathlib 4.32.2
- Verso Blueprint v4.32.0 for the documentation workspace

## Repository layout

```text
SYK/                       # repository and mathematical Lake package
├── SYK/                   # mathematical Lean modules, namespace SYK
│   ├── Analysis/
│   ├── Probability/
│   ├── Model/
│   ├── SuperConcentration/
│   └── CLT/               # Chaos, Quadratic, Limit, Log, and main results
├── Paper/                 # CLT_SYK.tex and its four sections
├── Notes/                 # lecture notes and their distributed PDF
├── Blueprint/             # SYKBlueprint package: document, generator entry point, four chapters
├── lakefile.toml           # mathlib-only mathematical package
└── workspace/             # parent ResearchWorkspace template
```

The CLTs assume the Gaussian AnnealedInput explicitly. See the CLT README (SYK/CLT/README.md) and the concentration README (SYK/SuperConcentration/README.md) for the current statements and verification commands.

## Setup instructions

Clone this repository into a shared workspace and copy the parent configuration template:

```bash
cd <working directory>
git clone git@github.com:TokyoProbabilityGroup/SYK.git
cp SYK/workspace/lakefile.toml .
cp SYK/workspace/lake-manifest.json .
cp SYK/workspace/lean-toolchain .
cp SYK/workspace/AGENTS.md .
lake exe cache get
```

Review existing parent files before overwriting them. Projects in the parent workspace share a single `.lake/packages/` directory to avoid downloading and storing duplicate copies of mathlib and other dependencies. Run the following commands from that parent directory. See [the workspace guide](workspace/README.md) for handoff and configuration details.

## Building and testing

```bash
lake build SYKBlueprint
lake build SYK
lake env lean SYK/SYK/CLT/Main.lean
```

`lake build SYKBlueprint` checks mathematics and Blueprint; `lake build SYK` checks mathematics only. [The workspace guide](workspace/README.md#template-files-and-targets) explains the targets and dependency configuration.

The CLTs are Lean-checked conditional on `AnnealedInput`; constructing that input remains separate. Build success alone does not establish agreement between the formal statements and every manuscript claim. After changing a Lean file, check it individually before the final workspace build.

For the main results, inspect their types and axiom dependencies in a Lean editor or scratch file using the parent workspace:

```lean
import SYK.CLT.StandardModel

#check SYK.CLT.partition_and_log_partition_clt
#print axioms SYK.CLT.partition_and_log_partition_clt
#check SYK.CLT.standard_partition_and_log_partition_clt
#print axioms SYK.CLT.standard_partition_and_log_partition_clt
```

Check the displayed assumptions, quantifier order, normalizations, and conclusions against the manuscript. Both theorems require an explicit `hFE : AnnealedInput ...`; `#print axioms` checks their axiom dependencies but does not prove this input. These statement and assumption checks are needed when assessing which manuscript claims the formalization verifies, in addition to routine builds.

## Blueprint

Generate HTML and check its references from the parent workspace:

```bash
lake lean SYK/Blueprint/SYKBlueprintMain.lean -- --run SYK/Blueprint/SYKBlueprintMain.lean --output SYK/_out/site
lake exe vbp check --site SYK/_out/site
```

After changing documentation or referenced declarations, check the affected chapters and both entry modules with Lean, then run these commands. `vbp check` verifies manifest, HTML cache, and internal-reference consistency; it does not prove mathematical claims.

Generated HTML is under `SYK/_out/site/html-multi/` and is ignored by Git. For an optional PDF, append `--pdf` to the renderer command; a compatible LuaLaTeX environment is required. To serve the generated HTML locally:

```bash
python3 -m http.server 8000 --bind 127.0.0.1 --directory SYK/_out/site/html-multi
```

Open `http://localhost:8000/`. [The workspace guide](workspace/README.md#blueprint-dependencies) explains the explicit renderer and platform details.

## Manuscript and notes

From `SYK/Paper/`, run `latexmk -pdf CLT_SYK.tex`. The four files under `Paper/sections/` can also be compiled independently from that directory; references defined in other sections may remain unresolved in standalone builds. From `SYK/Notes/`, run `latexmk -pdf note.tex`. The manuscript and Lean formalization have separate verification requirements.

## References

- [Spin glass by Lean](https://github.com/or4nge19/SpinGlass)
