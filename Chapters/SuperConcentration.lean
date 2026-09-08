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

The currently checked declarations retain a real energy scale 𝒥, with
nonnegativity or positivity imposed by the estimates that need it. The intended
standard normalization is the specialization 𝒥 = 1. Model-specific
moment-generating-function and separate one-sided tail theorems are not yet
part of the checked API and are therefore not asserted in this chapter.
:::

:::definition "scaled_syk_hamiltonian" (parent := "superconcentration") (uses := "interaction_hamiltonian") (lean := "SYK.couplingScale, SYK.normalizedHamiltonian")
Let $`\mathcal{P} = (N,q)` be valid SYK parameters and let
$`\mathcal{M}` be a Majorana system. For an energy scale
$`\mathcal{J} \in \mathbb{R}` and a coupling vector $`J`, set

$$`
c_{N,q}(\mathcal{J})
  = \mathcal{J}
    \sqrt{\frac{(q-1)!}{N^{q-1}}},
\qquad
H_{\mathcal{J}}(J)
  = \sum_{|I|=q} c_{N,q}(\mathcal{J}) J_I \Psi_I .
`

Here $`\Psi_I` is the interaction operator associated with $`I`.
:::

:::definition "syk_log_partition" (parent := "superconcentration") (uses := "partition_function, scaled_syk_hamiltonian") (lean := "SYK.logPartition")
For $`\beta \in \mathbb{R}_{\ge 0}`, define the real log-partition function by

$$`
F_{\beta,\mathcal{J}}(J)
  = \log \operatorname{Re}
      \operatorname{Tr} \exp\bigl(-\beta H_{\mathcal{J}}(J)\bigr).
`

The matrix representation is finite-dimensional and nonempty. Self-adjointness
of $`H_{\mathcal{J}}(J)` makes the real part inside the logarithm strictly
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
For coupling vectors $`J,V` and $`s \in \mathbb{R}`, the derivative along the
coupling line is

$$`
\frac{d}{dr} F_{\beta,\mathcal{J}}(J+rV)\bigg|_{r=s}
  =
  -\beta \operatorname{Re}
    \operatorname{Tr}\bigl(
      \rho_{\beta,H_{\mathcal{J}}(J+sV)}
      H_{\mathcal{J}}(V)
    \bigr),
`

where $`\rho_{\beta,H}` is the thermal density matrix.
:::

:::proof "syk_directional_derivative"
Differentiate the trace exponential along the affine coupling line and then
differentiate the real logarithm, using positivity of the partition function.
Cyclicity of the trace rewrites the resulting quotient as the thermal
expectation displayed above.
:::

:::theorem "syk_directional_gradient_bound" (parent := "superconcentration") (uses := "scaled_syk_hamiltonian") (lean := "SYK.abs_beta_expectation_normHam_sq_le_exact, SYK.abs_beta_expectation_normHam_le")
If $`\mathcal{J} \ge 0`, then for every density matrix $`\rho` and coupling
direction $`V`,

$$`
\left|
  \beta \operatorname{Re}
    \operatorname{Tr}\bigl(\rho H_{\mathcal{J}}(V)\bigr)
\right|
\le
\frac{|\beta|\mathcal{J}}{\sqrt{q}} \lVert V \rVert_2.
`

Before simplifying the finite-volume normalization, the square of the
left-hand side is bounded by

$$`
\bigl(\beta c_{N,q}(\mathcal{J})\bigr)^2
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
c_{N,q}(\mathcal{J})
\sqrt{\frac{\binom{N}{q-1}}{q}}
\le \frac{\mathcal{J}}{\sqrt{q}}
`

then gives the simplified constant.
:::

:::theorem "log_partition_lipschitz" (parent := "superconcentration") (uses := "syk_log_partition") (lean := "SYK.logPartition_lipschitz")
If $`\mathcal{J} \ge 0`, then $`F_{\beta,\mathcal{J}}` is Lipschitz on the
Euclidean coupling space with constant

$$`
L = \frac{|\beta|\mathcal{J}}{\sqrt{q}}.
`
:::

:::proof "log_partition_lipschitz" (uses := "syk_directional_derivative, syk_directional_gradient_bound")
Restrict $`F_{\beta,\mathcal{J}}` to the line segment joining two coupling
vectors. The formula {uses "syk_directional_derivative"}[] and the bound
{uses "syk_directional_gradient_bound"}[] control its derivative by $`L`
times the length of the segment. The one-dimensional mean value theorem gives
the Lipschitz estimate.
:::

:::theorem "log_partition_zero_inverse_temperature" (parent := "superconcentration") (uses := "syk_log_partition") (lean := "SYK.logPartition_eq_log_card_of_beta_zero, SYK.logPartition_tail_of_beta_zero")
If $`\beta=0`, then for every coupling vector $`J`,

$$`
F_{0,\mathcal{J}}(J)=\log d,
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

:::theorem "log_partition_concentration" (parent := "superconcentration") (uses := "syk_log_partition") (lean := "SYK.logPartition_two_sided_tail_standardGaussian")
Let the couplings be independent standard Gaussian variables. If
$`\mathcal{J}>0`, $`\beta \ne 0`, and $`t>0`, then

$$`
\mathbb P\left(
  \left|F_{\beta,\mathcal{J}}
    - \mathbb{E} F_{\beta,\mathcal{J}}\right|>t
\right)
\le
2\exp\left(
  -\frac{q t^2}{2\beta^2\mathcal{J}^2}
\right).
`
:::

:::proof "log_partition_concentration" (uses := "gaussian_two_sided_concentration, log_partition_lipschitz")
Apply the finite-dimensional Gaussian two-sided concentration theorem to
{uses "log_partition_lipschitz"}[] with
$`L=|\beta|\mathcal{J}/\sqrt{q}`, and simplify $`2L^2`.
The separate zero-inverse-temperature case is recorded in
{bpref "log_partition_zero_inverse_temperature"}[].
:::
