# Shared Lean Workspace Template

This directory contains the files to copy to the parent directory of the cloned `SYK` repository. That parent directory serves as a shared Lean workspace for multiple mathematical research libraries.

## Intended layout

```text
<workspace-root>/
├── AGENTS.md
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
├── .lake/                  # generated locally by Lake
└── SYK/                    # cloned repository
    ├── AGENTS.md
    ├── Annealed_FE/
    ├── Blueprint.lean
    ├── BlueprintMain.lean  # Blueprint renderer entry point
    ├── Chapters/
    ├── CLT/
    ├── Model/
    ├── Universality/
    ├── SuperConcentration/
    └── workspace/
```

The projects share one Lean toolchain, one Lake dependency manifest, and one downloaded mathlib cache. Sharing the workspace is an implementation and cache-management choice; it does not imply a mathematical dependency between the projects.

## Why use a shared workspace?

A separate Lake project normally maintains its own `.lake` directory and dependency checkout. Creating one for every research topic can duplicate large mathlib installations. This template instead provides one root toolchain, Lake configuration, dependency manifest, and cache for multiple mathematically independent libraries.

## Template files

- `lakefile.toml` defines the workspace package, pinned mathlib and Verso Blueprint dependencies, common Lean options, and Lean libraries under `SYK/`. A compatible new project should normally be added as another `lean_lib`, not as a nested Lake project.
- `lake-manifest.json` records exact resolved dependency revisions. It should normally be updated through Lake rather than edited manually.
- `lean-toolchain` fixes the Lean version shared by all libraries.
- `AGENTS.md` provides project-independent Codex instructions. At the workspace root, it is supplemented by files such as `SYK/AGENTS.md` and `SYK/CLT/AGENTS.md`.
- `README.md` documents this template and remains in `SYK/workspace/`.

`defaultTargets` selects the individual mathematical libraries and the `SYK` target for shared foundations and project documentation. No aggregate Lean import file is needed. The renderer `SYK/BlueprintMain.lean` stays in the repository; no project-specific Lean file needs to be copied to the workspace root.

## Initial setup

From the directory that will become the workspace root, run:

```bash
git clone git@github.com:TokyoProbabilityGroup/SYK.git
cp SYK/workspace/lakefile.toml .
cp SYK/workspace/lake-manifest.json .
cp SYK/workspace/lean-toolchain .
cp SYK/workspace/AGENTS.md .
lake exe cache get
lake build
lake lean SYK/BlueprintMain.lean -- --run SYK/BlueprintMain.lean --output SYK/_out/site
lake exe vbp check --site SYK/_out/site
```

Review existing root files before overwriting them. Lake creates `.lake/` locally; do not copy it into this template.

## Updating an existing workspace

The root copies are active; the files here are versioned templates. Compare them before applying changes:

```bash
diff -u lakefile.toml SYK/workspace/lakefile.toml
diff -u lake-manifest.json SYK/workspace/lake-manifest.json
diff -u lean-toolchain SYK/workspace/lean-toolchain
diff -u AGENTS.md SYK/workspace/AGENTS.md
```

Do not blindly overwrite root files when the workspace contains other projects. Merge relevant changes while preserving their libraries and instructions. A template change does not automatically update an existing workspace, and a local root change should be copied back only when it is appropriate for future users.

When migrating from the old layout, review the imports in the root `SYK.lean` and cover the required modules with Lake targets. Compare `SYKMain.lean` with `SYK/BlueprintMain.lean` and preserve local renderer changes. Update the root Lake configuration, then remove the two obsolete root files. Their template copies are no longer distributed. Existing output under the root `_out/site/` is from the old layout and is not used by the new commands.

Run `lake build` for the targets listed in `defaultTargets`. Individual targets such as `lake build Model SuperConcentration CLT` are unchanged. `lake build SYK` checks the shared foundations under `SYK/Probability/`, the Blueprint and chapter modules, and their dependencies; it does not replace the individual mathematical library targets. CI uses the same `defaultTargets` rather than maintaining a separate list.

Use the `lake lean` renderer command shown above, followed by `lake exe vbp check --site SYK/_out/site`. Lake builds the renderer's imports automatically. This explicitly selects the repository's renderer because the installed `vbp build` only discovers root-level entry points. Generated output stays under `SYK/_out/site/` and is ignored by Git. Append `--pdf` to the renderer command for an optional PDF. See the project README for local serving instructions and the reason for invoking the server separately.

## Adding another project

A project compatible with the current Lean and mathlib versions should normally be added as another directory and `lean_lib` in the root `lakefile.toml`. It should keep its mathematical instructions in its own `AGENTS.md`. If it requires incompatible versions, it may need a separate workspace.

## Files excluded from this template

Do not place `.lake/`, copied mathlib sources, compiled artifacts, editor or machine state, absolute local paths, secrets, LaTeX products, or project-specific proof plans here. Project-specific architecture and progress documents belong in the corresponding project directory, such as `SYK/CLT/`.
