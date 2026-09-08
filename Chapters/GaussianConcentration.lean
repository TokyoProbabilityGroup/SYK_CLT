import Verso
import VersoManual
import VersoBlueprint
import SYK.SuperConcentration.GaussianConcentration.GaussianConcentration

set_option linter.mathlibStandardSet false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Gaussian concentration" =>

:::group "gaussian_concentration"
Results for Lipschitz functions on finite-dimensional Euclidean spaces equipped
with the standard Gaussian measure.
:::

:::theorem "gaussian_subgaussian_mgf" (parent := "gaussian_concentration") (lean := "SYK.product_standardGaussian_hasSubgaussianMGF")
For a Lipschitz function with Lipschitz constant L, the centered random
variable is sub-Gaussian with parameter L² under the product standard
Gaussian measure.
:::

:::theorem "gaussian_two_sided_concentration" (parent := "gaussian_concentration") (uses := "gaussian_subgaussian_mgf") (lean := "SYK.euclidean_lipschitz_gaussian_concentration")
The sub-Gaussian moment-generating-function bound implies the corresponding
two-sided Gaussian tail estimate.
:::
