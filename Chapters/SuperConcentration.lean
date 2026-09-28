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
The model-specific argument that turns the algebraic relations of Majorana
interaction operators into concentration of the finite-dimensional SYK
log-partition function.

The checked declarations use the standard Hamiltonian shared by Model and
measure Lipschitz constants in the standard Gaussian coordinates. The
density-matrix estimate lives in `DensityMatrix`, the finite-size Majorana
bound in `MajoranaBound`, and the MGF and tail applications in `Main`.
:::

:::definition "syk_log_partition" (parent := "superconcentration") (uses := "partition_function, scaled_syk_hamiltonian") (lean := "SYK.logPartition")
For $`\beta \in \mathbb{R}_{\ge 0}`, define the real log-partition function by

$$`
F_{\beta}(g)
  = \log \operatorname{Re}
      \operatorname{Tr} \exp\bigl(-\beta H(g)\bigr).
`

The matrix representation is finite-dimensional and nonempty. Self-adjointness
of $`H(g)` makes the real part inside the logarithm strictly
positive.
:::

:::theorem "anticommuting_expectation_sum" (parent := "superconcentration") (lean := "SYK.sum_sq_expectation_le_one")
Let $`\rho` be a density matrix and let
$`\{A_i\}_{i \in \iota}` be a finite
family of self-adjoint matrices such that $`A_i^2=1` and
$`A_iA_j=-A_jA_i` whenever $`i \ne j`. Then

$$`
\sum_{i \in \iota}
  \left|\operatorname{Tr}(\rho A_i)\right|^2
  \le 1.
`
:::

:::proof "anticommuting_expectation_sum"
Put $`c_i=\operatorname{Tr}(\rho A_i)` and $`B=\sum_i c_iA_i`.
Self-adjointness makes each $`c_i` real. The anticommutation relations cancel
all cross terms and give $`B^2=(\sum_i |c_i|^2)1`. Positivity of the variance
of $`B` in the state $`\rho` yields $`s-s^2 \ge 0` for
$`s=\sum_i |c_i|^2`, hence $`s \le 1`.
:::

:::theorem "majorana_expectation_sum" (parent := "superconcentration") (uses := "majorana_system") (lean := "SYK.syk_sum_sq_expectation_le")
Assume $`q>0` is even. For every density matrix $`\rho` and every Majorana
system $`\mathcal{M}`,

$$`
\sum_{I : |I|=q}
  \left|\operatorname{Tr}(\rho \Psi_I)\right|^2
  \le \frac{\binom{N}{q-1}}{q}.
`
:::

:::proof "majorana_expectation_sum" (uses := "anticommuting_expectation_sum")
Fix a $`(q-1)`-element core $`C`. Extending $`C` by one label outside it
produces a family of self-adjoint involutions that pairwise anticommute, so
{uses "anticommuting_expectation_sum"}[] bounds the corresponding sum by one.
Sum this estimate over all cores. Every $`q`-element interaction occurs
exactly $`q` times, and division by $`q>0` gives the stated bound.
:::

:::theorem "syk_directional_derivative" (parent := "superconcentration") (uses := "syk_log_partition") (lean := "SYK.logPartition_line_deriv_eq")
For standard Gaussian coordinate vectors $`g,V` and $`s \in \mathbb{R}`,
the derivative along the coupling line is

$$`
\frac{d}{dr} F_{\beta}(g+rV)\bigg|_{r=s}
  =
  -\beta \operatorname{Re}
    \operatorname{Tr}\bigl(
      \rho_{\beta,H(g+sV)}
      H(V)
    \bigr),
`

where $`\rho_{\beta,H}` is the thermal density matrix.
:::

:::proof "syk_directional_derivative" (uses := "standard_hamiltonian_properties")
Differentiate the trace exponential along the affine coupling line and then
differentiate the real logarithm, using positivity of the partition function.
Cyclicity of the trace rewrites the resulting quotient as the thermal
expectation displayed above.
:::

:::theorem "syk_directional_gradient_bound" (parent := "superconcentration") (uses := "scaled_syk_hamiltonian") (lean := "SYK.abs_beta_expectation_normHam_sq_le_exact, SYK.abs_beta_expectation_normHam_le")
For every density matrix $`\rho` and standard Gaussian coordinate
direction $`V`,

$$`
\left|
  \beta \operatorname{Re}
    \operatorname{Tr}\bigl(\rho H(V)\bigr)
\right|
\le
\frac{\beta}{\sqrt{q}} \lVert V \rVert_2.
`

Before simplifying the finite-volume normalization, the square of the
left-hand side is bounded by

$$`
\bigl(\beta \sigma_N\bigr)^2
\frac{\binom{N}{q-1}}{q}
\lVert V \rVert_2^2.
`
:::

:::proof "syk_directional_gradient_bound" (uses := "majorana_expectation_sum")
Expand the expectation as a Euclidean inner product between $`V` and the
interaction expectations. Cauchy--Schwarz and
{uses "majorana_expectation_sum"}[] give the exact finite-volume bound. The
falling-factorial estimate

$$`
\sigma_N
\sqrt{\frac{\binom{N}{q-1}}{q}}
\le \frac{1}{\sqrt{q}}
`

then gives the simplified constant.
:::

:::theorem "log_partition_lipschitz" (parent := "superconcentration") (uses := "syk_log_partition") (lean := "SYK.logPartition_lipschitz")
$`F_{\beta}` is Lipschitz on the
Euclidean coupling space with constant

$$`
L = \frac{\beta}{\sqrt{q}}.
`
:::

:::proof "log_partition_lipschitz" (uses := "syk_directional_derivative, syk_directional_gradient_bound")
Restrict $`F_{\beta}` to the line segment joining two standard Gaussian coordinate
vectors. The formula {uses "syk_directional_derivative"}[] and the bound
{uses "syk_directional_gradient_bound"}[] control its derivative by $`L`
times the length of the segment. The one-dimensional mean value theorem gives
the Lipschitz estimate.
:::

:::theorem "log_partition_zero_inverse_temperature" (parent := "superconcentration") (uses := "syk_log_partition") (lean := "SYK.logPartition_eq_log_card_of_beta_zero, SYK.logPartition_centered_of_beta_zero, SYK.logPartition_tail_of_beta_zero")
If $`\beta=0`, then for every standard Gaussian coordinate vector $`g`,

$$`
F_0(g)=\log d,
`

where $`d` is the dimension of the matrix representation. Consequently, for
every $`t>0`, the centered two-sided deviation event has standard Gaussian
measure zero.
:::

:::proof "log_partition_zero_inverse_temperature"
At $`\beta=0`, the Gibbs operator is the identity, so its trace is the
dimension $`d`. The centered log-partition function therefore vanishes
identically, making every positive-deviation event empty.
:::

:::theorem "log_partition_mgf" (parent := "superconcentration") (uses := "syk_log_partition") (lean := "SYK.logPartition_hasSubgaussianMGF")
For every nonnegative inverse temperature and every real $`s`, the centered
log-partition function $`X=F_\beta-\mathbb E F_\beta` satisfies

$$`
\mathbb E e^{sX} \le \exp\left(\frac{s^2\beta^2}{2q}\right).
`

The `HasSubgaussianMGF` parameter is $`\beta^2/q`, including zero inverse
temperature. This is an upper bound parameter, not an assertion of equality
for the variance or of optimality. Expectation is with respect to the product
standard Gaussian coordinate measure.
:::

:::proof "log_partition_mgf" (uses := "gaussian_subgaussian_mgf, log_partition_lipschitz")
Apply the Gaussian Lipschitz MGF theorem with $`L=\beta/\sqrt q` and simplify
$`L^2=\beta^2/q`. Its zero-Lipschitz branch includes $`\beta=0`.
:::

:::theorem "log_partition_one_sided_concentration" (parent := "superconcentration") (uses := "syk_log_partition") (lean := "SYK.logPartition_upper_tail_standardGaussian, SYK.logPartition_lower_tail_standardGaussian")
For $`\beta>0` and $`t>0`, both one-sided deviations satisfy

$$`
\mathbb P(F_\beta-\mathbb E F_\beta>t)
\le e^{-qt^2/(2\beta^2)},\qquad
\mathbb P(\mathbb E F_\beta-F_\beta>t)
\le e^{-qt^2/(2\beta^2)}.
`

The declarations supply the SYK Lipschitz estimate internally. At zero inverse
temperature both positive-deviation events are empty, by
{bpref "log_partition_zero_inverse_temperature"}[].
:::

:::proof "log_partition_one_sided_concentration" (uses := "log_partition_lipschitz")
Apply the Gaussian upper and lower tail theorems with $`L=\beta/\sqrt q`.
Simplifying their exponent gives the stated bound.
:::

:::theorem "log_partition_concentration" (parent := "superconcentration") (uses := "syk_log_partition") (lean := "SYK.logPartition_two_sided_tail_standardGaussian")
Let the coordinates $`g_A` be independent standard Gaussian variables. If
$`\beta \ne 0` and $`t>0`, then

$$`
\mathbb P\left(
  \left|F_{\beta}
    - \mathbb{E} F_{\beta}\right|>t
\right)
\le
2\exp\left(
  -\frac{q t^2}{2\beta^2}
\right).
`
:::

:::proof "log_partition_concentration" (uses := "gaussian_two_sided_concentration, log_partition_lipschitz")
Apply the finite-dimensional Gaussian two-sided concentration theorem to
{uses "log_partition_lipschitz"}[] with
$`L=\beta/\sqrt{q}`, and simplify $`2L^2`.
The separate zero-inverse-temperature case is recorded in
{bpref "log_partition_zero_inverse_temperature"}[].
:::
