# SYK partition-function CLT

The source tree is grouped by role:

- `main_result.lean` contains the finite model, probabilistic notation, CLT statements, and paper-facing theorem.
- `external_inputs.lean` records results supplied by the high-temperature analysis.
- `coefficient_limit.lean` derives the radial coefficient limit from those inputs.
- `gaussian/radial_clt.lean` states the radial Gaussian limit.
- `lemmas/` contains reusable proofs and the remaining named internal estimates.
- `partition_function_clt.lean` exposes the partition-function and log-partition conditional conclusions.

Import `SYK.CLT.main_result` for the core definitions and standardized conclusion.
