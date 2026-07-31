# SYK partition-function CLT

The source tree is grouped by role:

- `definitions.lean` contains the finite model and probabilistic notation.
- `external_inputs.lean` records results supplied by the high-temperature analysis.
- `coefficient_limit.lean` derives the radial coefficient limit from those inputs.
- `gaussian/radial_clt.lean` states the radial Gaussian limit.
- `lemmas/` contains reusable proofs and the remaining named internal estimates.
- `partition_function_clt.lean` and `log_partition_function_clt.lean` expose the conditional conclusions.
- `main_result.lean` is the paper-facing standardized theorem.

Import `SYK.CLT` for the public development.
