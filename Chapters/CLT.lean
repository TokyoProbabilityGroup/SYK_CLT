import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Central limit theorem" =>

:::group "central_limit_theorem"
The asymptotic results for the partition function and its logarithm at fixed
even interaction order.
:::

:::theorem "partition_function_clt" (parent := "central_limit_theorem") (uses := "partition_function, log_partition_concentration")
After the prescribed normalization, the relative fluctuation of the partition
function converges in distribution to the Gaussian limit stated in the
manuscript.
:::

:::theorem "log_partition_clt" (parent := "central_limit_theorem") (uses := "partition_function_clt, log_partition_concentration")
The partition-function central limit theorem, the local linearization of the
logarithm, and control of the negative tail yield the corresponding central
limit theorem for the centered log-partition function.
:::

:::theorem "free_energy_law_of_large_numbers" (parent := "central_limit_theorem") (uses := "log_partition_concentration")
The normalized logarithm of the partition function converges almost surely to
the limiting free-energy quantity on the parameter range stated in the
manuscript. The manuscript proof and its precise external inputs remain to be
completed and audited.
:::
