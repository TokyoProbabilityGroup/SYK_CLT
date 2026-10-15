import Verso
import VersoManual
import VersoBlueprint
import SYK.Main
import SYK.CLT.Normalization
import SYK.CLT.StandardModel
import SYK.Probability.GaussianChaos.CoefficientIBP
import SYK.Probability.GaussianChaos.Basic
import SYK.CLT.Quadratic.GaussianQuadraticObservable
import SYK.CLT.Quadratic.IndependentFourthMoment
import SYK.Probability.GaussianChaos.Orthogonality
import SYK.Probability.GaussianChaos.HermiteDensity
import SYK.Probability.GaussianChaos.PolynomialDensity
import SYK.CLT.Chaos.SecondChaos

set_option linter.mathlibStandardSet false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Central limit theorem" =>

The manuscript is `Paper/CLT_SYK.tex`. The three groups correspond to
`gaussian-chaos.tex`, `higher-chaoses.tex`, and `main-results.tex`.
The standalone entry point
`SYK/Main.lean` states the model, annealed conditions, and both CLTs together.

:::group "clt_gaussian_chaos"
Gaussian chaos
:::

:::definition "clt_partition_function" (parent := "clt_gaussian_chaos") (uses := "scaled_syk_hamiltonian") (lean := "SYK.CLT.partitionFunction, SYK.CLT.realPartitionFunction, SYK.CLT.Setting, SYK.CLT.GaussianSYK.MajoranaOperators, SYK.CLT.GaussianSYK.Model, SYK.CLT.GaussianSYK.disorderLaw, SYK.CLT.GaussianSYK.Model.H, SYK.CLT.GaussianSYK.Model.Z, SYK.CLT.GaussianSYK.Model.varianceZ")
Fix even $`q\ge4` and a diverging sequence of even sizes $`N\ge q`.
At each size choose a Majorana representation of positive finite dimension $`d_N`.
For independent standard Gaussian coordinates $`G=(g_I)_{I\in\mathcal I_N}`,
where $`\mathcal I_N=\{I\subset[N]:|I|=q\}`, put
$$`
H_N(G)=\sigma_N\sum_{I\in\mathcal I_N}g_I\psi_I,\qquad
\sigma_N^2=\frac{(q-1)!}{N^{q-1}},\qquad
Z_N(z;G)=\frac1{d_N}\operatorname{Tr}e^{-zH_N(G)}.
`
For real $`\beta`, define $`Y_N(\beta)=Z_N(\beta)/\mathbb E Z_N(\beta)`
and note that $`|\mathcal I_N|=\binom Nq`.
The manuscript's `subsec:SYK-model` uses $`d_N=2^{N/2}`; the family here
also permits other representations of positive finite dimension.
:::

:::lemma_ "clt_finite_partition_properties" (parent := "clt_gaussian_chaos") (lean := "SYK.CLT.partitionFunction_zero, SYK.CLT.partitionFunction_eq_trace_div_card, SYK.CLT.partitionFunction_im_eq_zero, SYK.CLT.realPartitionFunction_pos")
For every finite model and real $`\beta`, $`Z_N(0;G)=1` and
$`Z_N(\beta;G)` is real and strictly positive. The ordinary partition
function is $`d_N Z_N`.
:::

:::proof "clt_finite_partition_properties" (uses := "clt_partition_function")
Diagonalize the self-adjoint Hamiltonian. The real inverse-temperature exponential
has positive eigenvalues, and their normalized sum is positive. At zero
inverse temperature the exponential is the identity.
:::

:::lemma_ "clt_standard_normalization" (parent := "clt_gaussian_chaos") (lean := "SYK.CLT.partitionFunction_standard")
For the standard representation, $`d_N=2^{N/2}`, so
$`Z_N(z;G)=2^{-N/2}\operatorname{Tr}e^{-zH_N(G)}` as in `subsec:SYK-model`.
:::

:::proof "clt_standard_normalization" (uses := "clt_partition_function, standard_representation_dimension")
The computational basis has $`2^{N/2}` elements; substitute its cardinality
into the dimension-normalized trace.
:::

:::lemma_ "clt_partition_moments" (parent := "clt_gaussian_chaos") (lean := "SYK.CLT.realPartitionFunction_moments, SYK.CLT.Setting.partition_moments")
For every real $`\beta` and finite model, $`Z_N(\beta)\in L^2`,
$`\log Z_N(\beta)` is integrable, and $`\mathbb E Z_N(\beta)>0`.
:::

:::proof "clt_partition_moments" (uses := "clt_trace_lower_bound")
The finite-dimensional disorder map is linear, so
$`Z_N(\beta;G)\le e^{C\|G\|_2}` for a finite nonnegative constant $`C`.
Gaussian exponential integrability controls the square.
The lower bound $`Z_N\ge1` bounds the logarithm between zero and $`C\|G\|_2`.
:::

:::lemma_ "clt_gaussian_hermite_ibp" (parent := "clt_gaussian_chaos") (lean := "SYK.GaussianChaos.hermite_coefficient_ibp, SYK.GaussianChaos.hermite_coefficient_integrable, SYK.GaussianChaos.hermiteMulti_pair_ibp, SYK.GaussianChaos.hermiteList_multiIndexList, SYK.GaussianChaos.partialList_perm, SYK.GaussianChaos.integral_hermiteMulti_eq_zero")
As in `lem:Gaussian-Hermite-IBP`, let $`\alpha` be a multi-index on a finite
coordinate set and $`f\in C^{|\alpha|}`. For each multi-index $`\eta\le\alpha` (componentwise),
assume $`|\partial^\eta f(G)|\le C_\eta e^{C_\eta\|G\|_2}` with $`C_\eta>0`.
For $`H_\alpha(G)=\prod_i\operatorname{He}_{\alpha_i}(G_i)`,
both sides are integrable and
$$`
\mathbb E[H_\alpha(G)f(G)]=\mathbb E[\partial^\alpha f(G)].
`
The Hermite polynomials have the probabilists' normalization.
:::

:::proof "clt_gaussian_hermite_ibp"
Apply the one-dimensional Gaussian integration-by-parts identity successively
to independent coordinates. Exponential integrability justifies every step.
Finite smoothness permits reordering partial derivatives, so each prefix uses
an index $`\eta\le\alpha`. The iterated creation operators give the same
Hermite products and also yield the identity for a pair of Hermite functions.
:::

:::lemma_ "clt_hermite_polynomial_span" (parent := "clt_gaussian_chaos") (lean := "SYK.GaussianChaos.realHermiteBasis, SYK.GaussianChaos.polynomialProdEval_mem_hermiteMulti_span, SYK.GaussianChaos.mvPolynomial_eval_mem_hermiteMulti_span, SYK.GaussianChaos.mvPolynomial_eval_memLp_and_hermiteSpan, SYK.GaussianChaos.hermiteOrthonormal_dense_of_mvPolynomialLp_dense")
Every real multivariate polynomial on a finite coordinate set is a finite
linear combination of products of probabilists' Hermite polynomials.
Its Gaussian $`L^2` class belongs to the same span.
:::

:::proof "clt_hermite_polynomial_span"
The monic Hermite polynomials form a basis of the one-variable polynomial space.
Expand products in this basis, then use induction on multivariate monomials.
Gaussian polynomial moments give the required $`L^2` membership.
:::

:::lemma_ "clt_exponential_moment_determination" (parent := "clt_gaussian_chaos") (lean := "SYK.Probability.measure_eq_of_moments, SYK.GaussianChaos.gaussianExpDual_memLp_two")
Finite real measures with all real exponential moments are determined by their
polynomial moments. Exponentials of continuous linear observables belong to
finite-product Gaussian $`L^2`.
:::

:::proof "clt_exponential_moment_determination"
The moment-generating function is analytic near zero. Equality of moments
gives equality there and then equality of characteristic functions, which
determines the measures. Gaussian exponential integrability proves the
$`L^2` assertion.
:::

:::lemma_ "clt_finite_hermite_projection" (parent := "clt_gaussian_chaos") (lean := "SYK.GaussianChaos.hermiteMulti_orthogonality, SYK.GaussianChaos.inner_hermiteLp, SYK.GaussianChaos.hermiteFiniteProjection_eq_starProjection, SYK.GaussianChaos.mem_multiIndicesOfDegree, SYK.GaussianChaos.hermiteOrthonormal_orthonormal, SYK.GaussianChaos.hasSum_hermiteDegreeProjection")
Hermite products satisfy
$$`
\mathbb E[H_\alpha H_\eta]=\alpha!\,\mathbf1_{\{\alpha=\eta\}},
\qquad \alpha!=\prod_i\alpha_i!.
`
For a finite set $`A` of multi-indices, the projection of $`f\in L^2` onto
their span is $`\sum_{\alpha\in A}\langle H_\alpha,f\rangle H_\alpha/\alpha!`.
Each fixed-degree set is finite. The normalized Hermite products are
orthonormal; if their span is dense, the degree projections sum to $`f`
in $`L^2`.
:::

:::proof "clt_finite_hermite_projection" (uses := "clt_gaussian_hermite_ibp")
Factor Gaussian integrals across coordinates and use one-variable Hermite
orthogonality. The finite projection formula follows from the exact squared
norm $`\alpha!`. The Hilbert-space expansion of a complete orthonormal family
gives the sum of degree projections.
:::

:::theorem "clt_hermite_complete" (parent := "clt_gaussian_chaos") (lean := "SYK.GaussianChaos.mvPolynomialLp_dense, SYK.GaussianChaos.hermiteOrthonormal_dense, SYK.GaussianChaos.hasSum_hermiteCoefficients_unconditional, SYK.GaussianChaos.hasSum_hermiteDegreeProjection_unconditional")
Real multivariate polynomial classes are dense in finite-product Gaussian
$`L^2`. Thus the normalized Hermite products form a complete orthonormal
family, and
$$`
f=\sum_{r=0}^\infty\sum_{|\alpha|=r}
\frac{\mathbb E[fH_\alpha]}{\alpha!}H_\alpha
`
in Gaussian $`L^2`, as in `eq: chaos`.
:::

:::proof "clt_hermite_complete" (uses := "clt_hermite_polynomial_span, clt_exponential_moment_determination, clt_finite_hermite_projection")
If a function is orthogonal to polynomials, its positive and negative weighted
Gaussian measures have identical moments under every linear projection.
Exponential moment determination and characteristic-function uniqueness make
these measures equal. The function is therefore zero. Polynomial span and
orthogonality now give Hermite completeness and the grouped expansion.
:::

:::proposition "clt_exact_second_chaos" (parent := "clt_gaussian_chaos") (lean := "SYK.CLT.Setting.Y_firstChaos_eq_zero, SYK.CLT.Setting.Y_secondChaos_eq, SYK.CLT.Setting.Z_sign_gauge, SYK.CLT.Setting.integral_Z_mul_hermite_eq_zero_pi, SYK.CLT.Setting.inner_offDiagonal_secondChaos_eq_zero, SYK.CLT.Setting.Y_secondChaos_eq_integral_sum, SYK.CLT.Setting.integral_Y_mul_sq_sub_one_eq, SYK.CLT.Setting.meanZ_hasDerivAt")
For every real $`\beta`, `prop:exact-second-chaos` gives
$$`
P_1Y_N=0,\qquad
P_2Y_N=\frac{\beta\,\partial_\beta\log\mathbb E Z_N}{2|\mathcal I_N|}
\sum_{I\in\mathcal I_N}(g_I^2-1).
`
Here $`\operatorname{He}_2(x)=x^2-1` and
$`\mathbb E[\operatorname{He}_2(g_I)^2]=2`.
:::

:::proof "clt_exact_second_chaos" (uses := "clt_partition_moments, clt_gaussian_hermite_ibp")
Following `lem: parity rule lemma`, define $`\Gamma=\psi_1\cdots\psi_N`.
It is unitary, and for even $`N` it anticommutes with every $`\psi_j`.
For a real unit vector $`v`, set $`C_v=\sum_jv_j\psi_j` and $`U_v=\Gamma C_v`.
Then $`U_v\psi_jU_v^*=\psi_j-2v_jC_v`.
The choice $`v=e_j` gives the same reflection as $`\psi_j\Gamma`,
which differs by a sign; $`v=(e_a-e_b)/\sqrt2` gives a transposition.
Composing these conjugations gives signed-permutation invariance of $`Z_N`.
Sign changes remove the first chaos and the off-diagonal quadratic coefficients.
Vertex permutations and Gaussian invariance make all diagonal coefficients equal.
Gaussian integration by parts and $`Z_N(\beta;tG)=Z_N(t\beta;G)` identify
their sum with $`\beta\,\partial_\beta\mathbb E Z_N`.
Locally uniform exponential bounds justify differentiating the expectation.
Divide by the positive mean to obtain the formula.
:::

:::group "clt_higher_chaoses"
Higher chaoses
:::

:::lemma_ "clt_partition_higher_derivatives" (parent := "clt_higher_chaoses") (lean := "SYK.CLT.Setting.abs_partialMulti_Z_le, SYK.CLT.Setting.partialMulti_Z_exp_growth, SYK.CLT.Setting.hermite_coefficient_Z_eq_integral_partialMulti, SYK.CLT.Setting.abs_inner_hermiteLp_YGaussianLp_le")
For every interaction multi-index $`\alpha` and real $`\beta`,
`lem:Z-derivative-bound` states
$$`
|\partial_G^\alpha Z_N(\beta;G)|
\le (|\beta|\sigma_N)^{|\alpha|}Z_N(\beta;G).
`
All derivatives have at most exponential growth. Hermite integration by parts therefore
bounds $`|\mathbb E[Y_NH_\alpha]|\le(|\beta|\sigma_N)^{|\alpha|}`.
:::

:::proof "clt_partition_higher_derivatives" (uses := "clt_gaussian_hermite_ibp, clt_partition_moments, interaction_involutions")
The manuscript uses the iterated Duhamel formula from
`eq:iterated-Duhamel-formula`: there are $`k!` ordered words over a simplex
of volume $`1/k!`. The normalized Schatten–Hölder inequality bounds each word by $`Z_N`,
since every $`\psi_I` has operator norm one.
The corresponding matrix derivative estimate also follows from the exponential
power series and Schatten bounds. Pull it through the real part and the linear
disorder map. Smoothness, at most exponential growth, and Hermite integration by parts
then give the coefficient bound.
:::

:::lemma_ "clt_rademacher_encoding" (parent := "clt_higher_chaoses") (lean := "SYK.CLT.Rademacher.even_sum_rademacher_moment, SYK.CLT.Rademacher.rademacher_encoding")
For independent Rademacher signs, define
$`S_{N,q}=\sum_{I\in\mathcal I_N}\prod_{x\in I}\varepsilon_x`.
A multi-index is even when $`\sum_{I\ni x}\alpha_I` is even for every vertex $`x`.
For every integer $`r\ge0`, `eq:even-sum-Rademacher-moment` gives
$$`
\sum_{|\alpha|=r,\ \alpha\ \mathrm{even}}\frac1{\alpha!}
=\frac1{r!}\mathbb E_\varepsilon[S_{N,q}^r].
`
For fixed even $`q\ge4`, there are $`c_q>0` and finite $`C_q` depending
only on $`q` such that for every $`N` and every $`0\le t\le c_qN^{-(q-1)}`,
`eq:Rademacher-exponential-moment` gives
$$`
\mathbb E_\varepsilon[|S_{N,q}|^3e^{t|S_{N,q}|}]
\le C_qN^{3q/2}.
`
:::

:::proof "clt_rademacher_encoding"
Expand $`S_{N,q}^r` by the multinomial formula. Independence makes each
vertex product's expectation one precisely for even multi-indices, and zero
otherwise. For the exponential estimate, Newton's identities give
$`|S_{N,q}|\le C_q(N^{q/2}+|\sum_x\varepsilon_x|^q)`.
With $`X_N=N^{-1/2}\sum_x\varepsilon_x` and small $`c_q`,
$`t|S_{N,q}|\le(1+|X_N|^2)/4`.
Hoeffding's bound controls the polynomially weighted exponential moment
uniformly in $`N`. This is `lem:Rademacher-encoding`.
:::

:::lemma_ "clt_degree_projection_bound" (parent := "clt_higher_chaoses") (lean := "SYK.CLT.Setting.norm_sq_hermiteDegreeProjection_le_even_sum, SYK.CLT.Setting.norm_sq_hermiteDegreeProjection_le_rademacher_moment")
For every degree $`r`, `eq:Hermite-Rademacher-bound` and
its Rademacher form give
$$`
\|P_rY_N(\beta)\|_2^2
\le(\beta^2\sigma_N^2)^r
\sum_{|\alpha|=r,\ \alpha\ \mathrm{even}}\frac1{\alpha!}
=\frac{(\beta^2\sigma_N^2)^r}{r!}\mathbb E_\varepsilon[S_{N,q}^r].
`
:::

:::proof "clt_degree_projection_bound" (uses := "clt_exact_second_chaos, clt_partition_higher_derivatives, clt_rademacher_encoding, clt_hermite_complete")
Use the exact factorial norm of each Hermite product.
Parity removes odd multi-indices, the derivative bound controls the remaining
coefficients, and the Rademacher counting identity gives the last equality.
:::

:::lemma_ "clt_higher_chaos_moment_sum" (parent := "clt_higher_chaoses") (lean := "SYK.CLT.Setting.sum_higherChaosProjection_le_exp_moment, SYK.CLT.Setting.tsum_higherChaosProjection_le_exp_moment")
With $`t_N=\beta^2\sigma_N^2`, `eq:all-higher-chaoses-at-once` gives
$$`
\sum_{r\ge3}\|P_rY_N(\beta)\|_2^2
\le\frac{t_N^3}{6}
\mathbb E_\varepsilon[|S_{N,q}|^3e^{t_N|S_{N,q}|}].
`
:::

:::proof "clt_higher_chaos_moment_sum" (uses := "clt_degree_projection_bound, clt_rademacher_encoding")
Sum the finite-degree estimates and bound the exponential tail by
$`\sum_{r\ge3}u^r/r!\le u^3e^u/6` for $`u\ge0`.
Pass from finite partial sums to the nonnegative infinite sum.
:::

:::proposition "clt_higher_chaos_closure" (parent := "clt_higher_chaoses") (lean := "SYK.CLT.Setting.tsum_higherChaosProjection_le_power, SYK.CLT.Setting.higherChaosProjection_isLittleO")
There is $`\beta_{\mathrm r}(q)>0` such that for every fixed real
$`|\beta|<\beta_{\mathrm r}`, `prop:higher-chaos-closure` gives
$$`
\sum_{r\ge3}\|P_rY_N(\beta)\|_2^2
=O(N^{-3(q/2-1)})=o(N^{2-q}).
`
:::

:::proof "clt_higher_chaos_closure" (uses := "clt_higher_chaos_moment_sum, clt_rademacher_encoding")
Choose $`\beta_{\mathrm r}=\sqrt{c_q/(q-1)!}`.
Then $`t_N=\beta^2(q-1)!N^{-(q-1)}` lies in the Rademacher
exponential-moment range. Combine that estimate with the infinite-series bound:
$`t_N^3N^{3q/2}=O(N^{-3(q/2-1)})`.
For $`q\ge4`, the exponent is strictly larger than $`q-2`.
:::

:::group "clt_main_results"
Proof of the main results
:::

:::theorem "clt_expected_pressure_limit" (parent := "clt_main_results")
For each fixed real $`\beta`, `thm: input` gives a deterministic limit
$$`
N^{-1}\log\mathbb E Z_N(\beta)\longrightarrow\ell_q(\beta),
`
and $`\ell_q` is differentiable on $`\mathbb R`.
The source is He2026 v3, Theorem 1.1 and Proposition 3.3, as cited in the manuscript.
:::

:::lemma_ "clt_convex_derivative_transfer" (parent := "clt_main_results")
In `lem:convex-derivatives`, differentiable convex functions
$`h_N:\mathbb R\to\mathbb R` converge pointwise to $`h\in C^1(\mathbb R)`.
Then $`h_N\to h` and $`h_N'\to h'` locally uniformly on $`\mathbb R`.
The manuscript cites Rockafellar (1970), Theorems 10.8 and 25.7, and omits the proof.
:::

:::proposition "clt_annealed_free_energy" (parent := "clt_main_results")
As in `prop:annealed-free-energy`, there is an even convex
$`\ell_q\in C^1(\mathbb R)` such that, locally uniformly for real $`\beta`,
$$`
\frac1N\log\mathbb E Z_N(\beta)\longrightarrow\ell_q(\beta),\qquad
\frac1N\partial_\beta\log\mathbb E Z_N(\beta)\longrightarrow\ell_q'(\beta).
`
Moreover, $`\beta\ell_q'(\beta)>0` for every $`\beta\ne0`.
:::

:::proof "clt_annealed_free_energy" (uses := "clt_expected_pressure_limit, clt_convex_derivative_transfer")
Gaussian symmetry and $`Z_N(0)=1` extend the positive inverse-temperature pressure
limit to the real line. The normalization conversion is
$`\ell_q(\beta)=p_q(2^{q/2}|\beta|)` for $`\beta\ne0`,
with $`\ell_q(0)=0`, as in `eq:He-normalization-conversion`.
The external Schwinger–Dyson derivative formula and positive Lehmann
representation in `eq:ell-kernel-derivative` and `eq:ell-kernel-representation`
give $`0<\ell_q'(\beta)\le\beta/q` for $`\beta>0`.
Evenness gives the sign on the negative half-line, and this derivative bound
gives $`C^1` regularity at zero. The second derivative of the finite annealed
pressure is a spectral variance divided by $`N`, hence nonnegative.
Apply the convex derivative convergence lemma to obtain both locally uniform
limits.
:::

:::definition "gaussian_annealed_input" (parent := "clt_main_results") (uses := "clt_annealed_free_energy") (lean := "SYK.CLT.AnnealedInput, SYK.CLT.GaussianSYK.AnnealedInput")
For one model family, collect the conditions of `prop:annealed-free-energy`:
an even convex $`C^1` limit $`\ell_q` on $`\mathbb R`, locally uniform
convergence of the annealed pressure and its derivative, and
$`\beta\ell_q'(\beta)>0` for every nonzero real $`\beta`.
The following asymptotic results take these conditions as their input.
:::

:::lemma_ "clt_conditional_annealed_limit" (parent := "clt_main_results") (uses := "gaussian_annealed_input") (lean := "SYK.CLT.annealedFreeEnergy_tendsto, SYK.CLT.annealedDerivative_tendsto, SYK.CLT.secondChaosCoefficient_tendsto, SYK.CLT.Setting.secondChaosScaledCoefficient_tendsto")
For a family satisfying the annealed conditions, the pressure and its
derivative converge for every real $`\beta`. The scaled quadratic coefficient
satisfies
$$`
N^{q/2-1}
\frac{\beta\,\partial_\beta\log\mathbb E Z_N(\beta)}{\sqrt{2|\mathcal I_N|}}
\longrightarrow\sqrt{\frac{q!}{2}}\,\beta\ell_q'(\beta).
`
:::

:::proof "clt_conditional_annealed_limit" (uses := "gaussian_annealed_input")
Use the derivative convergence from the input and the fixed-order asymptotic
$`|\mathcal I_N|=\binom Nq\sim N^q/q!`. This is the coefficient limit in the proof of
`thm:partition-clt`.
:::

:::lemma_ "clt_conditional_nondegeneracy" (parent := "clt_main_results") (uses := "gaussian_annealed_input") (lean := "SYK.CLT.limitVariance_pos_of_ne_zero")
For $`\beta\ne0`, the annealed sign condition gives positive limiting variance
$$`
v_q(\beta)=\frac{q!}{2}\beta^2(\ell_q'(\beta))^2>0.
`
:::

:::proof "clt_conditional_nondegeneracy" (uses := "gaussian_annealed_input")
Both $`q!` and the square of the nonzero number $`\beta\ell_q'(\beta)`
are positive.
:::

:::lemma_ "clt_gaussian_quadratic_observable" (parent := "clt_main_results") (lean := "SYK.CLT.centeredGaussianSquare_mean, SYK.CLT.centeredGaussianSquare_second_moment, SYK.CLT.normalizedQuadraticSum_law")
For a standard Gaussian $`g`, $`(g^2-1)/\sqrt2` has mean zero and
second moment one. The normalized finite sum has the same law in product
coordinates and in the Euclidean coupling space.
:::

:::proof "clt_gaussian_quadratic_observable"
Use the second and fourth standard Gaussian moments, then transport the
coordinate product measure through the Euclidean coordinate identification.
:::

:::lemma_ "clt_gaussian_quadratic_moments" (parent := "clt_main_results") (lean := "SYK.CLT.centeredGaussianSquare_fourth_moment, SYK.CLT.normalizedGaussianSquares_fourth_moment, SYK.CLT.normalizedGaussianSquares_fourth_moment_le")
For a standard Gaussian $`g`, $`(g^2-1)/\sqrt2` has fourth moment $`15`.
For $`M>0` independent coordinates, put
$`U_M=(2M)^{-1/2}\sum_{i=1}^M(g_i^2-1)`. Then
$`\mathbb E U_M^4=3+12/M\le15`, as used in the proof of
`thm:free-energy-clt`.
:::

:::proof "clt_gaussian_quadratic_moments" (uses := "clt_gaussian_quadratic_observable")
Expand the fourth power. Independence and zero means leave only terms with
four equal indices or two pairs. The same finite-law correspondence transports
the moment bound to Euclidean coupling coordinates.
:::

:::lemma_ "clt_gaussian_quadratic_sum" (parent := "clt_main_results") (lean := "SYK.CLT.Setting.interactionCard_tendsto, SYK.CLT.Setting.normalizedQuadraticSum_clt")
With $`|\mathcal I_N|=\binom Nq`,
$$`
U_N=\frac1{\sqrt{2|\mathcal I_N|}}\sum_{I\in\mathcal I_N}(g_I^2-1)
\Longrightarrow\mathcal N(0,1).
`
:::

:::proof "clt_gaussian_quadratic_sum" (uses := "clt_gaussian_quadratic_observable")
The summands are independent with mean zero and variance one after
normalization. The classical i.i.d. CLT applies as $`|\mathcal I_N|\to\infty`.
Equivalently, the finite product characteristic function and its quadratic
Taylor limit give this convergence on the varying coupling spaces.
:::

:::lemma_ "clt_second_chaos_and_remainder" (parent := "clt_main_results") (lean := "SYK.CLT.Setting.Y_decomposition, SYK.CLT.Setting.Y_zeroChaos, SYK.CLT.Setting.Y_secondChaos_eq_quadraticGaussianLp, SYK.CLT.Setting.scaled_Y_decomposition, SYK.CLT.Setting.higherChaosRemainderLp_norm_sq, SYK.CLT.Setting.scaled_higherChaosRemainderLp_norm_tendsto_zero, SYK.CLT.Setting.quadraticGaussianLp_clt, SYK.CLT.Setting.scaledQuadraticGaussianLp_clt, SYK.Probability.tendstoInDistribution_mul_coeff, SYK.Probability.varying_l2_perturb_clt, SYK.CLT.Setting.relativeFluctuation_clt, SYK.CLT.Setting.varianceY_pi_decomposition, SYK.CLT.Setting.scaled_varianceZ_over_mean_sq_tendsto, SYK.CLT.Setting.varianceZ_pos_of_ne_zero, SYK.CLT.Setting.standardizedFluctuation_clt")
As in `eq:Y-decomposition-final`,
$$`
Y_N-1=c_NU_N+\mathcal R_N,\qquad
c_N=\frac{\beta\,\partial_\beta\log\mathbb E Z_N}{\sqrt{2|\mathcal I_N|}},
\qquad \mathcal R_N=\sum_{r\ge3}P_rY_N.
`
The remainder is orthogonal to $`U_N` and
$`\|\mathcal R_N\|_2^2=\sum_{r\ge3}\|P_rY_N\|_2^2`.
For sufficiently small fixed $`|\beta|`, this is $`O(N^{-3(q/2-1)})`,
and $`N^{q/2-1}\mathcal R_N\to0` in $`L^2`.
Moreover, $`\operatorname{Var}(Y_N)=c_N^2+\|\mathcal R_N\|_2^2`.
:::

:::proof "clt_second_chaos_and_remainder" (uses := "clt_exact_second_chaos, clt_hermite_complete, clt_higher_chaos_closure")
The constant chaos is one, the first chaos vanishes, and the exact second-chaos
formula identifies its projection with $`c_NU_N`.
Hermite completeness identifies the remaining tail; orthogonality gives its
squared norm and the variance decomposition. The higher-chaos closure makes
the scaled tail vanish.
:::

:::theorem "partition_function_clt" (parent := "clt_main_results") (uses := "gaussian_annealed_input") (lean := "SYK.CLT.partition_clt, SYK.CLT.GaussianSYK.syk_partition_clt")
For a family satisfying the annealed conditions, there is $`\beta_q>0` such
that for real $`0<|\beta|<\beta_q`, `thm:partition-clt` gives
$$`
N^{q/2-1}(Y_N(\beta)-1)\Longrightarrow\mathcal N(0,v_q(\beta)),\qquad
\frac{Z_N(\beta)-\mathbb E Z_N(\beta)}
{\sqrt{\operatorname{Var}Z_N(\beta)}}\Longrightarrow\mathcal N(0,1),
\qquad v_q(\beta)=\frac{q!}{2}\beta^2(\ell_q'(\beta))^2>0.
`
The finite-size variances are positive.
Of the two linked partition statements, only the abstract theorem includes
$`N^{-1}\log\mathbb E Z_N(\beta)\to\ell_q(\beta)`; the standalone
partition theorem asserts the CLTs and positivity.
:::

:::proof "partition_function_clt" (uses := "clt_second_chaos_and_remainder, clt_gaussian_quadratic_sum, clt_conditional_annealed_limit, clt_conditional_nondegeneracy")
The quadratic CLT, coefficient limit, and vanishing scaled remainder give the
relative CLT by Slutsky's theorem. Orthogonality gives
$`N^{q-2}\operatorname{Var}(Y_N)\to v_q(\beta)>0`.
Together with $`\operatorname{Var}(Y_N)=\operatorname{Var}(Z_N)/(\mathbb E Z_N)^2`,
this yields the standardized CLT. Finite-size positivity follows from the
nonconstant partition function for nonzero inverse temperature.
:::

:::lemma_ "clt_trace_lower_bound" (parent := "clt_main_results") (lean := "SYK.CLT.interactionOperator_trace_eq_zero, SYK.CLT.normalizedHamiltonian_normalizedTrace_eq_zero, SYK.CLT.realPartitionFunction_ge_one")
For each finite model and real $`\beta`,
$`\operatorname{tr}H_N(G)=0` and $`Z_N(\beta;G)\ge1`, as used in the
proof of `thm:free-energy-clt`.
:::

:::proof "clt_trace_lower_bound" (uses := "clt_finite_partition_properties, interaction_involutions")
Choose a vertex in an even-degree interaction. Conjugation by its Majorana
generator changes the interaction's sign, so its trace is zero.
The Hamiltonian is therefore traceless. Jensen's inequality on its real
eigenvalues gives $`Z_N\ge e^{-\beta\operatorname{tr}H_N}=1`.
:::

:::lemma_ "clt_relative_and_log_moments" (parent := "clt_main_results") (lean := "SYK.CLT.Setting.Y_pos, SYK.CLT.Setting.Y_memLp, SYK.CLT.Setting.Y_integrable, SYK.CLT.Setting.integral_Y, SYK.CLT.Setting.log_Y_eq, SYK.CLT.Setting.log_Y_integrable, SYK.CLT.Setting.integral_log_Y, SYK.CLT.Setting.centered_log_Y_eq, SYK.CLT.Setting.log_Z_nonneg, SYK.CLT.Setting.log_meanZ_nonneg, SYK.CLT.Setting.neg_log_Y_le_log_meanZ")
For every real $`\beta`, $`Y_N>0`, $`Y_N\in L^2`, $`\mathbb E Y_N=1`,
and $`\log Y_N` is integrable. Moreover,
$$`
\log Y_N=\log Z_N-\log\mathbb E Z_N,\qquad
\log Y_N-\mathbb E\log Y_N=\log Z_N-\mathbb E\log Z_N.
`
Also $`\log Z_N\ge0`, $`\log\mathbb E Z_N\ge0`, and
$`-\log Y_N\le\log\mathbb E Z_N`.
:::

:::proof "clt_relative_and_log_moments" (uses := "clt_partition_moments, clt_trace_lower_bound")
Divide the finite partition function by its positive mean. Integrability
and the logarithm-of-a-quotient identity give the centering formulas.
Use $`Z_N\ge1` for the remaining inequalities.
:::

:::lemma_ "clt_zero_inverse_temperature" (parent := "clt_main_results") (lean := "SYK.CLT.Setting.meanZ_zero, SYK.CLT.Setting.Y_zero, SYK.CLT.Setting.meanLogZ_zero, SYK.CLT.Setting.relativeFluctuation_zero, SYK.CLT.Setting.logFluctuation_zero, SYK.CLT.Setting.varianceZ_zero")
At $`\beta=0`, $`Z_N=\mathbb E Z_N=Y_N=1`.
Both logarithms and both relative and centered logarithmic fluctuations vanish.
The variance is zero, so this point is excluded from standardization.
:::

:::proof "clt_zero_inverse_temperature" (uses := "clt_partition_function")
The Hamiltonian exponent is zero, and the normalized trace of the identity
is one. Substitute this constant into the expectations, fluctuations, and variance.
:::

:::lemma_ "clt_log_centering_error" (parent := "clt_main_results") (uses := "gaussian_annealed_input") (lean := "SYK.CLT.Setting.cubed_scale_Y_lt_half_bounded, SYK.CLT.Setting.integral_log_Y_isBigO, SYK.CLT.Setting.scaled_sq_Y_lt_half_tendsto_zero, SYK.CLT.Setting.scaled_integral_logLinearError_tendsto_zero, SYK.CLT.Setting.scaled_centered_logLinearError_l1_tendsto_zero")
For a family satisfying the annealed conditions, fix nonzero sufficiently
small real $`\beta` and put $`a=q/2-1` and $`W_N=\log Y_N`.
The estimates in the proof of `thm:free-energy-clt` give
$$`
\mathbb E(Y_N-1)^2=O(N^{-2a}),\qquad
\mathbb P(Y_N<1/2)=O(N^{-3a}),\qquad
\mathbb E W_N=O(N^{-2a})=o(N^{-a}).
`
The scaled mean and centered $`L^1` errors of logarithmic linearization
tend to zero. Constants may depend on the fixed $`\beta`.
:::

:::proof "clt_log_centering_error" (uses := "clt_relative_and_log_moments, clt_second_chaos_and_remainder, clt_gaussian_quadratic_moments, clt_conditional_annealed_limit")
Decompose $`Y_N-1=c_NU_N+\mathcal R_N` with $`c_N=O(N^{-a})`.
The uniform fourth moment of $`U_N` and the second moment of the remainder
bound the small event by $`O(N^{-3a})`.
For $`h(y)=y-1-\log y`, the region $`y\ge1/2` satisfies
$`h(y)\le(y-1)^2`. On the small event, $`Z_N\ge1` implies
$`h(Y_N)\le-\log Y_N\le\log\mathbb E Z_N=O(N)`.
Since $`a\ge1`, both contributions are $`O(N^{-2a})`.
The identity $`-\mathbb E W_N=\mathbb E h(Y_N)` and the same bound
give the vanishing scaled mean and centered $`L^1` error.
:::

:::theorem "log_partition_clt" (parent := "clt_main_results") (uses := "gaussian_annealed_input") (lean := "SYK.CLT.partition_and_log_partition_clt, SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt, SYK.CLT.GaussianSYK.syk_log_partition_clt")
For the same family and a common positive $`\beta_q`, real
$`0<|\beta|<\beta_q` satisfies `thm:free-energy-clt`:
$$`
N^{q/2-1}\bigl(\log Z_N(\beta)-\mathbb E\log Z_N(\beta)\bigr)
\Longrightarrow\mathcal N\!\left(0,\frac{q!}{2}\beta^2(\ell_q'(\beta))^2\right).
`
The joint theorem asserts one positive radius for both CLTs; the individual
standalone statements are its projections.
:::

:::proof "log_partition_clt" (uses := "partition_function_clt, clt_log_centering_error")
The relative CLT makes $`N^a(Y_N-1)` tight and $`Y_N-1\to0` in probability.
On $`|Y_N-1|\le1/2`, the logarithmic Taylor error is bounded by
$`|N^a(Y_N-1)|\,|Y_N-1|` after scaling, so it vanishes in probability.
The centering estimate controls $`N^a\mathbb E\log Y_N`.
Slutsky's theorem now gives the logarithmic CLT. Take the smaller of the
positive radii for the partition and logarithmic conclusions.
:::

:::corollary "clt_standard_model_application" (parent := "clt_main_results") (uses := "gaussian_annealed_input") (lean := "SYK.CLT.standardSetting, SYK.CLT.standardSetting_size_iff, SYK.CLT.standardSetting_Z, SYK.CLT.standard_partition_and_log_partition_clt")
For the standard representation at sizes $`N_n=q+2n`, every even size
$`N\ge q` occurs exactly once. Assuming the annealed conditions for this
family, `thm:partition-clt` and `thm:free-energy-clt` hold with one common
positive radius, the manuscript's normalization, scaling and centering,
and positive limiting and finite-size variances.
:::

:::proof "clt_standard_model_application" (uses := "clt_standard_normalization, partition_function_clt, log_partition_clt")
The sizes diverge, and the standard basis cardinality identifies the
normalized trace with that of `subsec:SYK-model`.
Apply the joint conditional theorem to this family.
:::
