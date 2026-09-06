import Verso
import VersoManual
import VersoBlueprint
import SYK.SuperConcentration.Main

set_option linter.mathlibStandardSet false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Concentration of the SYK log-partition function" =>

:::group "superconcentration"
The model-specific estimates that connect Majorana interaction operators with
the general Gaussian concentration theorem.
:::

:::theorem "majorana_expectation_sum" (parent := "superconcentration") (uses := "majorana_system") (lean := "SYK.syk_sum_sq_expectation_le")
For a density matrix, the sum of squared expectations of the prescribed
Majorana interaction operators satisfies the finite-volume upper bound used in
the Lipschitz estimate.
:::

:::theorem "log_partition_lipschitz" (parent := "superconcentration") (uses := "interaction_hamiltonian, partition_function, majorana_expectation_sum") (lean := "SYK.logPartition_lipschitz")
As a function of the independent standard Gaussian couplings, the logarithm of
the partition function has the required uniform Lipschitz bound.
:::

:::theorem "log_partition_concentration" (parent := "superconcentration") (uses := "gaussian_two_sided_concentration, log_partition_lipschitz") (lean := "SYK.logPartition_two_sided_tail_standardGaussian")
The finite-dimensional SYK log-partition function satisfies the two-sided
Gaussian concentration inequality with the model-specific constant.
:::
