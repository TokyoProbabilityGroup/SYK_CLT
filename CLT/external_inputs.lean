import SYK.CLT.context
import SYK.CLT.lemmas.external_inputs

set_option autoImplicit false

/-!
This module is the public boundary for results imported from the
high-temperature literature.  The assumptions are fields of
`HighTemperatureInputs`, so downstream theorems remain conditional until
proofs of those fields are supplied.
-/
