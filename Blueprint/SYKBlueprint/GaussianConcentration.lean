import Verso
import VersoManual
import VersoBlueprint
import SYK.Probability.GaussianConcentration.Lipschitz

set_option linter.mathlibStandardSet false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Gaussian concentration" =>

:::group "gaussian_concentration"
Gaussian concentration
:::

:::theorem "gaussian_subgaussian_mgf" (parent := "gaussian_concentration") (lean := "SYK.GaussianConcentration.product_standardGaussian_hasSubgaussianMGF")
Let $`F` be a real Lipschitz function on a finite-dimensional Euclidean space
with standard Gaussian measure and Lipschitz constant $`L\ge0`.
For every $`s\in\mathbb R`,
$$`
\mathbb E e^{s(F-\mathbb E F)}\le e^{s^2L^2/2}.
`
The centered function is sub-Gaussian with parameter $`L^2`.
If $`L=0`, $`F` is constant and its centered version is zero.
:::

:::proof "gaussian_subgaussian_mgf"
For positive $`L`, smooth approximation preserves the Lipschitz bound.
Gaussian integration by parts gives the smooth covariance estimate; the
exponential differential inequality yields the MGF bound.
Pass to the Lipschitz function using Gaussian exponential integrability.
For $`L=0`, substitute the constant function.
:::

:::corollary "gaussian_two_sided_concentration" (parent := "gaussian_concentration") (lean := "SYK.GaussianConcentration.euclidean_lipschitz_gaussian_concentration, SYK.GaussianConcentration.product_standardGaussian_upper_tail, SYK.GaussianConcentration.product_standardGaussian_lower_tail")
For $`L>0` and $`t>0`,
$$`
\mathbb P(F-\mathbb E F>t)\le e^{-t^2/(2L^2)},\qquad
\mathbb P(\mathbb E F-F>t)\le e^{-t^2/(2L^2)},\qquad
\mathbb P(|F-\mathbb E F|>t)\le2e^{-t^2/(2L^2)}.
`
:::

:::proof "gaussian_two_sided_concentration" (uses := "gaussian_subgaussian_mgf")
Apply the exponential Markov inequality with $`s=t/L^2`.
Apply the same bound to $`-F` for the lower tail, then take the union
of the two one-sided events.
:::
