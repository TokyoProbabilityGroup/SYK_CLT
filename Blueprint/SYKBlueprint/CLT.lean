import Verso
import VersoManual
import VersoBlueprint
import SYK.CLT.Main
import SYK.CLT.Normalization
import SYK.CLT.StandardModel
import SYK.Analysis.ConvexDerivatives
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

:::group "central_limit_theorem"
Gaussian SYK partition-function and log-partition fluctuations at fixed even
$`q\ge4`. The manuscript is `Paper/CLT_SYK.tex` with its four included
sections. The proof of `thm:free-energy-clt` is in `main-results.tex`.

Finite-model results, conditional consequences of an external annealed input,
and the external expected-pressure statement have different status below.
:::

:::definition "clt_partition_function" (parent := "central_limit_theorem") (uses := "scaled_syk_hamiltonian") (lean := "SYK.CLT.partitionFunction, SYK.CLT.realPartitionFunction, SYK.CLT.Setting")
Fix even $`q\ge4`. For each even $`N\ge q`, choose a nonempty finite
matrix Majorana representation of dimension $`d_N`. The Gaussian coordinates
$`g_I` are independent and standard normal, and

$$`
H_N(g)=\sigma_N\sum_{|I|=q}g_I\Psi_I,
\qquad \sigma_N^2=\frac{(q-1)!}{N^{q-1}},
\qquad Z_N(z;g)=\frac{1}{d_N}\operatorname{Tr}\exp(-zH_N(g)).
`

For real $`\beta`, Lean uses the real part of $`Z_N(\beta;g)` to define
$`Y_N=Z_N/\mathbb E Z_N` and its fluctuations. `Setting q` allows any
diverging sequence of even sizes and a separate Gaussian coupling space at
each size. The manuscript's `subsec:SYK-model` uses the standard
$`d_N=2^{N/2}` representation. The abstract CLT takes this family as its
only model input and assumes `hFE : AnnealedInput q S` separately.
:::

:::theorem "clt_finite_partition_properties" (parent := "central_limit_theorem") (uses := "clt_partition_function") (lean := "SYK.CLT.partitionFunction_zero, SYK.CLT.partitionFunction_eq_trace_div_card, SYK.CLT.partitionFunction_im_eq_zero, SYK.CLT.realPartitionFunction_pos")
The normalized partition function satisfies $`Z_N(0;g)=1`, agrees with the
shared ordinary-trace partition function after division by $`d_N`, and is
real and strictly positive at every real inverse temperature. These
finite-dimensional statements in `FiniteModel.lean` have Lean proofs
without `sorryAx` for any nonempty finite matrix Majorana representation.
:::

:::theorem "clt_standard_normalization" (parent := "central_limit_theorem") (uses := "clt_partition_function, standard_representation") (lean := "SYK.CLT.partitionFunction_standard")
Specialization to the standard representation gives the coefficient
$`(2^{N/2})^{-1}` by `standardBasis_card`, as in `subsec:SYK-model`.
This finite correspondence theorem is in `Normalization.lean`; the abstract
CLT proof does not import it and does not use representation independence.
:::

:::theorem "clt_partition_moments" (parent := "central_limit_theorem") (uses := "clt_trace_lower_bound") (lean := "SYK.CLT.realPartitionFunction_moments, SYK.CLT.Setting.partition_moments")
For each real $`\beta` and size, $`Z_N\in L^2`, $`\log Z_N` is
integrable, and $`\mathbb E Z_N>0`. These Lean proofs have no `sorryAx`
and need no annealed input. The finite theorem takes only `Params` and
`MajoranaSystem`; its family consequence applies it to `S.majorana n`.
The Hamiltonian is a continuous linear map
of the finite-dimensional Gaussian coordinates, so
$`Z_N(\beta;g)\le\exp(C\|g\|)` for a finite nonnegative constant
depending on the model and temperature. Gaussian exponential
integrability controls the square, while $`1\le Z_N` bounds the
logarithm between zero and $`C\|g\|`.
:::

:::definition "gaussian_annealed_input" (parent := "central_limit_theorem") (lean := "SYK.CLT.AnnealedInput")
For one Gaussian model family `S : Setting q`, this structure contains
the convergence, regularity, and sign assertions of
`prop:annealed-free-energy`: an even convex $`C^1` limit on the whole real
line, locally uniform convergence of the normalized pressure and derivative,
and $`\beta\ell_q'(\beta)>0` for nonzero real $`\beta`.

The conditional CLTs receive these assertions as an explicit assumption
for `S`. Constructing an instance for a concrete family is outside the
conditional CLT proof and the agreed formalization scope.
:::

:::theorem "clt_conditional_annealed_limit" (parent := "central_limit_theorem") (uses := "gaussian_annealed_input") (lean := "SYK.CLT.annealedFreeEnergy_tendsto, SYK.CLT.annealedDerivative_tendsto, SYK.CLT.secondChaosCoefficient_tendsto, SYK.CLT.Setting.secondChaosScaledCoefficient_tendsto")
Given `S : Setting q` and `hFE : AnnealedInput q S`, Lean proves convergence
of the annealed pressure and its derivative, and the second-chaos
coefficient limit, for every real $`\beta`. The fixed-order binomial
asymptotic gives the exact scaled coefficient limit
$`\sqrt{q!/2}\,\beta\ell_q'(\beta)`. The input contains the convergence,
regularity, and sign assertions of `prop:annealed-free-energy` for this
one family, with no additional pressure or derivative bounds as assumptions.
Constructing `hFE` is outside the conditional CLT proof.
:::

:::theorem "clt_convex_derivative_transfer" (parent := "central_limit_theorem") (lean := "SYK.Analysis.convex_convergence_deriv_tendstoUniformlyOn")
The Lean convexity lemma gives locally uniform convergence of derivatives
when locally uniform convergence of differentiable convex functions to a
$`C^1` limit is already known. The manuscript's `lem:convex-derivatives`
also derives locally uniform convergence of the functions from pointwise
convergence. That first step remains unformalized and is outside the agreed
formalization scope.
:::

:::theorem "clt_conditional_nondegeneracy" (parent := "central_limit_theorem") (uses := "clt_conditional_annealed_limit") (lean := "SYK.CLT.exists_small_temperature_sign, SYK.CLT.exists_small_temperature_variance_pos")
The sign field in `hFE` gives
$`\beta\ell'(\beta)>0` for every nonzero real $`\beta`, and hence positive
limiting variance. These are verified conditional Lean results.
They do not imply positive variance at every finite size.
:::

:::theorem "clt_gaussian_hermite_ibp" (parent := "central_limit_theorem") (lean := "SYK.GaussianConcentration.hermiteMulti_ibp_of_expGrowth, SYK.GaussianConcentration.hermiteMulti_ibp_integrable, SYK.GaussianConcentration.hermiteMulti_pair_ibp, SYK.GaussianConcentration.hermiteMulti_eq_prod, SYK.GaussianConcentration.partialList_perm, SYK.GaussianChaos.hermite_coefficient_ibp, SYK.GaussianChaos.integral_hermiteMulti_eq_zero")
The general identity in `lem:Gaussian-Hermite-IBP` is proved for any finite
coordinate set and independent standard Gaussian coordinates. Let
$`\alpha` be a nonnegative integer multi-index and let
$`f\in C^{|\alpha|}(\mathbb R^\iota;\mathbb R)`. For each
$`\eta\le\alpha` componentwise, assume there is $`C_\eta>0` such that
$`|\partial_G^\eta f(G)|\le C_\eta\exp(C_\eta\|G\|_2)` for every $`G`.
Then both expectations below are integrable and

$$`
\mathbb E\left[\left(\prod_{i\in\iota}\operatorname{He}_{\alpha_i}(G_i)\right)
f(G)\right]=\mathbb E[\partial_G^\alpha f(G)].
`

The Hermite polynomials have the probabilists' normalization. The proof
uses the shared selected-coordinate Gaussian Stein identity, exponential
integrability, and iteration of the creation operator. Polynomial factors
and their coordinate derivatives satisfy the necessary growth bounds.
Finite smoothness permits reordering partial derivatives, so every prefix
of the iteration is covered by an index $`\eta\le\alpha`. No growth
assumption on any other derivative is required. The identity and both
integrability statements have Lean proofs without `sorryAx`, also for
zero order and an empty coordinate set.

The checked bridge to the sign-parity module identifies its Hermite
normalization and Gaussian measure with those above. It also proves that
Hermite functions of positive total degree have mean zero and that
pairwise Hermite products are integrable. The orthogonality and finite
projection results in `eq: chaos` are recorded in the next node.
Integration by parts for a pair of Hermite functions is also checked;
polynomial closure supplies its growth hypotheses.

The specialization to $`Z_N` is recorded below: its smoothness and
all-order derivative growth estimates are checked in Lean.
:::

:::theorem "clt_hermite_polynomial_span" (parent := "central_limit_theorem") (lean := "SYK.GaussianChaos.realHermiteBasis, SYK.GaussianChaos.polynomialProdEval_mem_hermiteMulti_span, SYK.GaussianChaos.mvPolynomial_eval_mem_hermiteMulti_span, SYK.GaussianChaos.mvPolynomial_eval_memLp_and_hermiteSpan, SYK.GaussianChaos.hermiteOrthonormal_dense_of_mvPolynomialLp_dense")
For a finite coordinate set, every real multivariate polynomial function is
a finite real linear combination of products of probabilists' Hermite
polynomials. Lean proves this first for a product of one-variable
polynomials, then for arbitrary multivariate polynomials by induction on
monomials. The polynomial functions define Gaussian $`L^2` classes in the
span of the Hermite classes. Polynomial density and unconditional
Hermite completeness are proved in the node below.
:::

:::theorem "clt_exponential_moment_determination" (parent := "central_limit_theorem") (lean := "SYK.Probability.measure_eq_of_moments, SYK.GaussianChaos.gaussianExp_memLp_two, SYK.GaussianChaos.gaussianLp_integrable_mul_exp")
Finite real measures with every real exponential moment are determined by
their polynomial moments. Lean proves this through the analytic moment
generating function and characteristic-function uniqueness. Real
exponentials belong to standard Gaussian $`L^2`, and their products with
arbitrary Gaussian $`L^2` functions are integrable. Applying moment
determination to every linear projection proves polynomial density below.
:::

:::theorem "clt_finite_hermite_projection" (parent := "central_limit_theorem") (uses := "clt_gaussian_hermite_ibp") (lean := "SYK.GaussianChaos.hermiteMulti_orthogonality, SYK.GaussianChaos.inner_hermiteLp, SYK.GaussianChaos.hermiteFiniteProjection_eq_starProjection, SYK.GaussianChaos.mem_multiIndices_degree, SYK.GaussianChaos.hermiteOrthonormal_orthonormal, SYK.GaussianChaos.hasSum_hermiteDegreeProjection")
For every finite set of standard Gaussian coordinates, the probabilists'
Hermite products satisfy

$$`
\mathbb E[H_\alpha(G)H_\eta(G)]
=\mathbf1_{\{\alpha=\eta\}}\prod_i\alpha_i!.
`

For any finite set $`S` of multi-indices and real $`f\in L^2(\gamma)`, the
orthogonal projection onto $`\operatorname{span}\{H_\alpha:\alpha\in S\}`
is the finite coefficient sum

$$`
\sum_{\alpha\in S}
\frac{\langle H_\alpha,f\rangle}{\prod_i\alpha_i!}H_\alpha.
`

The set $`\{\alpha:|\alpha|=r\}` is finite, so this applies to each
homogeneous degree. Normalizing each Hermite product by its $`L^2` norm
gives a checked orthonormal family. Under the explicit assumption that its
span is dense in Gaussian $`L^2`, Lean proves that the infinite sum of
degree projections converges to $`f` in $`L^2`. The required density
is supplied by the next node. The linked Lean declarations have no
`sorryAx`.
:::

:::theorem "clt_hermite_complete" (parent := "central_limit_theorem") (uses := "clt_hermite_polynomial_span, clt_exponential_moment_determination, clt_finite_hermite_projection") (lean := "SYK.GaussianChaos.gaussianMonomialLp_dense, SYK.GaussianChaos.mvPolynomialLp_dense, SYK.GaussianChaos.hermiteOrthonormal_dense, SYK.GaussianChaos.hasSum_hermiteCoefficients_unconditional, SYK.GaussianChaos.hasSum_hermiteDegreeProjection_unconditional")
For every finite coordinate set $`\iota`, real multivariate polynomial
classes are dense in $`L^2(\gamma_\iota)`. Orthogonality to polynomials
implies vanishing moments under every real continuous linear observable.
The positive and negative weighted Gaussian measures then agree after
every such projection by moment determination, and hence agree by
characteristic-function uniqueness. Thus the normalized Hermite products
form a complete orthonormal family. For every real
$`f\in L^2(\gamma_\iota)`, the factorial-coefficient expansion and
its grouping by total degree both converge to $`f` in Gaussian $`L^2`.
This proves `eq: chaos`, interpreted as an equality in Gaussian $`L^2`,
with the manuscript's Hermite and Gaussian normalizations.
:::

:::theorem "clt_exact_second_chaos" (parent := "central_limit_theorem") (uses := "clt_partition_moments, clt_gaussian_hermite_ibp") (lean := "SYK.CLT.Setting.Y_firstChaos_eq_zero, SYK.CLT.Setting.Y_secondChaos_eq")
For every real inverse temperature and every finite model in `Setting q`,
the manuscript's `prop:exact-second-chaos` holds in Gaussian $`L^2`:
$`P_1Y_N=0` and
$`P_2Y_N=\frac{\beta\partial_\beta\log\mathbb E Z_N}{2M_N}\sum_I(g_I^2-1)`.
The normalization is $`M_N=\binom Nq`, with $`H_2(x)=x^2-1`
and $`\mathbb E H_2(g_I)^2=2`.
:::

:::proof "clt_exact_second_chaos" (uses := "clt_partition_moments, clt_gaussian_hermite_ibp")
The manuscript's generalized `lem: parity rule lemma` treats sign changes
and vertex permutations together. For a real unit vector $`v`, write
$`C_v=\sum_jv_j\psi_j` and $`U_v=\Gamma C_v`. The common identity
$`U_v\psi_jU_v^*=\psi_j-2v_jC_v` gives a coordinate sign change for
$`v=e_x` and a transposition for $`v=(e_a-e_b)/\sqrt2`.
Composing these unitaries and using invariance of the normalized trace
proves the manuscript's signed-permutation invariance. This common
reflection construction is a manuscript proof, not a newly checked Lean
declaration; the checked finite-model results used below are unchanged.
Sign-gauge symmetry removes odd Hermite coefficients and all off-diagonal
quadratic terms. Signed vertex transpositions preserve the normalized trace
and Gaussian measure. Their transitivity on interactions proves equality
of the diagonal coefficients in
`SYK.CLT.Setting.integral_Y_mul_sq_sub_one_eq`.
First-order Gaussian integration by parts gives
$`\mathbb E[Z_N(g_I^2-1)]=\mathbb E[g_I\partial_{g_I}Z_N]`.
The scaling identity $`Z_N(\beta;tG)=Z_N(t\beta;G)` identifies their sum.
Smoothness and locally uniform exponential bounds justify differentiating
the expectation in `SYK.CLT.Setting.meanZ_hasDerivAt`.
Dividing by the positive mean gives the stated coefficient, including at
$`\beta=0`. These finite-model results require no annealed-limit input.
:::

:::theorem "clt_partition_higher_derivatives" (parent := "central_limit_theorem") (uses := "clt_gaussian_hermite_ibp, clt_partition_moments") (lean := "SYK.CLT.Setting.abs_partialMulti_Z_le, SYK.CLT.Setting.partialMulti_Z_exp_growth, SYK.CLT.Setting.hermite_coefficient_Z_eq_integral_partialMulti, SYK.CLT.Setting.abs_inner_hermiteLp_YGaussianLp_le")
For every interaction multi-index $`\alpha`, the normalized partition
function satisfies the bound in `eq:Z-derivative-bound`:

$$`
|\partial_G^\alpha Z_N(\beta;G)|
\le (|\beta|\sigma_N)^{|\alpha|}Z_N(\beta;G).
`

Here $`\sigma_N` is the coupling scale of the shared model. The proof
pulls the checked iterated trace-exponential derivative estimate through
the real part and the linear disorder map. The matrix estimate is proved
using its power series and Schatten bounds. The manuscript's Duhamel
simplex integral representation is not separately formalized. Exponential growth and
smoothness permit Gaussian Hermite integration by parts for every
$`\alpha`. The resulting Hermite coefficient of $`Y_N` is bounded by
$`(|\beta|\sigma_N)^{|\alpha|}`. These Lean declarations have no
`sorryAx` dependency.
:::

:::theorem "clt_rademacher_encoding" (parent := "central_limit_theorem") (lean := "SYK.CLT.Rademacher.even_sum_rademacher_moment, SYK.CLT.Rademacher.rademacher_encoding")
For the degree-$`q` elementary symmetric polynomial $`S_{N,q}` in
independent Rademacher signs, Lean proves `eq:even-sum-Rademacher-moment`:

$$`
\sum_{|\alpha|=r,\ \alpha\ \mathrm{even}}\frac1{\alpha!}
=\frac1{r!}\mathbb E_\varepsilon[S_{N,q}^r].
`

For even $`q\ge4`, it also proves `eq:Rademacher-exponential-moment` with
constants depending only on $`q` and the stated range
$`0\le t\le c_q N^{-(q-1)}`. Both declarations were checked without
`sorryAx`; the full higher-chaos sum remains separate.
:::

:::theorem "clt_degree_projection_bound" (parent := "central_limit_theorem") (uses := "clt_partition_higher_derivatives, clt_rademacher_encoding, clt_hermite_complete") (lean := "SYK.CLT.Setting.norm_sq_hermiteDegreeProjection_le_even_sum, SYK.CLT.Setting.norm_sq_hermiteDegreeProjection_le_rademacher_moment")
For every homogeneous degree $`r`, the Gaussian $`L^2` projection of
$`Y_N` satisfies `eq:Hermite-Rademacher-bound` and its Rademacher form:

$$`
\|P_rY_N(\beta)\|_2^2
\le \frac{(\beta^2\sigma_N^2)^r}{r!}
\mathbb E_\varepsilon[S_{N,q}^r].
`

The result uses the exact factorial norm of each Hermite product, parity
of the coefficients, the all-order derivative bound, and the finite
Rademacher counting identity. The next node sums these checked
finite-degree bounds.
:::

:::theorem "clt_higher_chaos_moment_sum" (parent := "central_limit_theorem") (uses := "clt_degree_projection_bound, clt_rademacher_encoding") (lean := "SYK.CLT.Setting.sum_higherChaosProjection_le_exp_moment, SYK.CLT.Setting.tsum_higherChaosProjection_le_exp_moment")
Put $`t_N=\beta^2\sigma_N^2`. The checked infinite-series estimate is

$$`
\sum_{r\ge3}\|P_rY_N(\beta)\|_2^2
\le \frac{t_N^3}{6}\mathbb E_\varepsilon
\left[|S_{N,q}|^3e^{t_N|S_{N,q}|}\right].
`

The proof first bounds finite partial sums using the factorial-weighted
Rademacher identity and the exponential-series tail inequality, then
passes to the nonnegative infinite sum. The next node supplies the
high-temperature radius and the resulting power of $`N`.
:::

:::theorem "clt_higher_chaos_closure" (parent := "central_limit_theorem") (uses := "clt_higher_chaos_moment_sum, clt_rademacher_encoding") (lean := "SYK.CLT.Setting.tsum_higherChaosProjection_le_power, SYK.CLT.Setting.higherChaosProjection_isLittleO")
For some $`\beta_{\mathrm{r}}>0` and all $`|\beta|<\beta_{\mathrm{r}}`,

$$`
\sum_{r\ge3}\|P_rY_N(\beta)\|_2^2
=O\bigl(N^{-3(q/2-1)}\bigr)=o(N^{2-q}).
`

Both the uniform pointwise power bound and the little-o statement are
checked in Lean. The radius comes from the Rademacher exponential-moment
constant and the coupling variance $`(q-1)!N^{-(q-1)}`.
:::

:::theorem "clt_gaussian_quadratic_observable" (parent := "central_limit_theorem") (lean := "SYK.CLT.centeredGaussianSquare_mean, SYK.CLT.centeredGaussianSquare_second_moment, SYK.CLT.normalizedQuadraticSum_law")
For a standard Gaussian $`g`, the observable $`(g^2-1)/\sqrt2` has
mean zero and second moment $`1`. The normalized finite sum has the
same law on the product-Gaussian space and the shared Euclidean
coupling space. These statements require neither an asymptotic CLT
nor `AnnealedInput`.
:::

:::theorem "clt_gaussian_quadratic_moments" (parent := "central_limit_theorem") (uses := "clt_gaussian_quadratic_observable") (lean := "SYK.CLT.centeredGaussianSquare_fourth_moment, SYK.CLT.normalizedGaussianSquares_fourth_moment, SYK.CLT.Setting.normalizedQuadraticSum_fourth_moment_le")
For a standard Gaussian $`g`, the observable $`(g^2-1)/\sqrt2` has
mean zero, second moment $`1`, and fourth moment $`15`. For $`M>0`
independent coordinates, the normalized sum has fourth moment
$`3+12/M\le15`. Its product-Gaussian law agrees with its law on the
shared Euclidean coupling space. These finite moment identities are
checked independently of the quadratic CLT and `AnnealedInput`.
They provide the fourth-moment bound used in the logarithmic transfer
in the manuscript's proof of `thm:free-energy-clt`.
:::

:::theorem "clt_gaussian_quadratic_sum" (parent := "central_limit_theorem") (uses := "clt_gaussian_quadratic_observable") (lean := "SYK.CLT.Setting.interactionCard_tendsto, SYK.CLT.Setting.normalizedQuadraticSum_clt")
With $`M_N=\binom Nq`, the centered quadratic Gaussian sum

$$`
\frac{1}{\sqrt{2M_N}}\sum_{I\in\mathcal I_N}(g_I^2-1)
`

converges in distribution to $`\mathcal N(0,1)` under the shared Gaussian
coupling measure. The checked proof uses the finite product characteristic
function, its quadratic Taylor limit, and $`M_N\to\infty`.
:::

:::theorem "clt_second_chaos_and_remainder" (parent := "central_limit_theorem") (uses := "clt_exact_second_chaos, clt_higher_chaos_closure")
The manuscript's `prop:exact-second-chaos` identifies the leading Gaussian
chaos of $`Y_N-1`. Its `prop:higher-chaos-closure` bounds the remainder by
$`\|\mathcal R_N\|_2^2=O(N^{-3a})`, where $`a=q/2-1`.
The proof uses parity symmetry, Gaussian integration by parts,
the trace-exponential derivative bound, and Rademacher encoding of the higher-chaos sum.
The sign-gauge symmetry of the scaled, normalized finite-model partition
function is checked as `SYK.CLT.Setting.Z_sign_gauge`. The odd Hermite
coefficient vanishes for its Gaussian coupling measure by
`SYK.CLT.Setting.integral_Z_mul_hermite_eq_zero`. The exact first-chaos
conclusion for $`Y_N` is `SYK.CLT.Setting.Y_firstChaos_eq_zero`.
For distinct interactions $`I\ne J`, the corresponding degree-two Hermite
coefficient of $`Y_N` vanishes by
`SYK.CLT.Setting.inner_offDiagonal_secondChaos_eq_zero`.
`SYK.CLT.Setting.Y_secondChaos_eq_integral_sum` gives the finite-size
second-chaos projection as a sum over interactions: the term at $`I` is
$`\frac12\mathbb E[Y_N(G)(g_I^2-1)](g_I^2-1)` in Gaussian $`L^2`.
The common coefficient is identified by the checked exact second-chaos
theorem above. All-order derivatives, Rademacher moments, and the
infinite-series bound, high-temperature radius, and the
$`N^{-3(q/2-1)}=o(N^{2-q})` estimate are now checked. The actual $`L^2`
remainder is identified by `SYK.CLT.Setting.higherChaosRemainderLp_norm_sq`,
and its scaled norm tends to zero by
`SYK.CLT.Setting.scaled_higherChaosRemainderLp_norm_tendsto_zero`.
`SYK.CLT.Setting.Y_zeroChaos` and `SYK.CLT.Setting.Y_decomposition`
give the constant projection and the exact quadratic-plus-remainder
decomposition. `SYK.CLT.Setting.Y_secondChaos_eq_quadraticGaussianLp`
identifies the quadratic term with the normalized Gaussian-square sum.
`SYK.CLT.Setting.scaled_Y_decomposition` gives its exact scaled form,
and `SYK.CLT.Setting.quadraticGaussianLp_clt` gives the sum's limit
on the product Gaussian space.
The changing scalar is handled by
`SYK.Probability.tendstoInDistribution_mul_coeff`, giving
`SYK.CLT.Setting.scaledQuadraticGaussianLp_clt` under `AnnealedInput`
for nonzero inverse temperature.
`SYK.Probability.varying_l2_perturb_clt` transfers the vanishing tail despite
the varying coupling spaces. `SYK.CLT.Setting.relativeFluctuation_clt`
states the resulting relative CLT on the model's Euclidean coupling space
with the manuscript's exact `limitVariance`.
`SYK.CLT.Setting.varianceY_pi_decomposition` gives the exact finite-size
quadratic-plus-remainder variance, and
`SYK.CLT.Setting.scaled_varianceZ_over_mean_sq_tendsto` proves convergence
of the normalized partition variance to `limitVariance`.
`SYK.CLT.Setting.varianceZ_pos_of_ne_zero` proves finite-size positivity,
and `SYK.CLT.Setting.standardizedFluctuation_clt` gives the standardized
Gaussian limit. The partition-function theorem is checked independently
of the logarithmic transfer.
:::

:::theorem "partition_function_clt" (parent := "central_limit_theorem") (uses := "clt_second_chaos_and_remainder, clt_gaussian_quadratic_sum, clt_conditional_nondegeneracy") (lean := "SYK.CLT.partition_clt")
Assume `S : Setting q` and `hFE : AnnealedInput q S`. The Lean statements
choose $`0<\beta_q` so that, for real
$`0<|\beta|<\beta_q`, the annealed pressure converges to $`\ell(\beta)` and

$$`
N^{q/2-1}(Y_N(\beta)-1)
\Longrightarrow
\mathcal N\!\left(0,\frac{q!}{2}\beta^2\ell'(\beta)^2\right).
`

The statements also require positive limiting variance,
positive variance at every finite size, and a standardized CLT. At
$`\beta=0`, the relative fluctuation vanishes and standardization is undefined;
this point is outside the CLT statements.
The joint declaration and both individual CLTs are Lean-checked without
`sorryAx`, conditional on `hFE`.
The manuscript and Lean impose the same nonzero-inverse-temperature restriction.
:::

:::theorem "clt_trace_lower_bound" (parent := "central_limit_theorem") (uses := "clt_finite_partition_properties") (lean := "SYK.CLT.interactionOperator_trace_eq_zero, SYK.CLT.normalizedHamiltonian_normalizedTrace_eq_zero, SYK.CLT.realPartitionFunction_ge_one")
In the proof of `thm:free-energy-clt`, conjugation by a Majorana
generator makes every even-degree interaction traceless. Hence
$`\operatorname{tr}H_N=0`, and Jensen's inequality gives
$`Z_N(\beta;g)\ge1` for real $`\beta`. These statements are proved
in Lean without `sorryAx` for any nonempty finite matrix Majorana
representation. The spectral proof sums $`1+x\le e^x` over eigenvalues
whose sum is zero.
:::

:::theorem "clt_relative_and_log_moments" (parent := "central_limit_theorem") (uses := "clt_partition_moments, clt_trace_lower_bound") (lean := "SYK.CLT.Setting.Y_pos, SYK.CLT.Setting.Y_memLp, SYK.CLT.Setting.Y_integrable, SYK.CLT.Setting.integral_Y, SYK.CLT.Setting.log_Y_eq, SYK.CLT.Setting.log_Y_integrable, SYK.CLT.Setting.integral_log_Y, SYK.CLT.Setting.centered_log_Y_eq, SYK.CLT.Setting.log_Z_nonneg, SYK.CLT.Setting.log_meanZ_nonneg, SYK.CLT.Setting.neg_log_Y_le_log_meanZ")
For every real inverse temperature, $`Y_N=Z_N/\mathbb E Z_N` is positive,
belongs to $`L^2`, and has expectation one. Its logarithm is integrable,
and

$$`
\log Y_N=\log Z_N-\log\mathbb E Z_N,
\qquad
\log Y_N-\mathbb E\log Y_N=\log Z_N-\mathbb E\log Z_N.
`

Moreover, $`\log Z_N\ge0`, $`\log\mathbb E Z_N\ge0`, and
$`-\log Y_N\le\log\mathbb E Z_N`. These finite-model inputs to
`thm:free-energy-clt` are proved without `sorryAx`. They do not supply
the asymptotic estimate $`\log\mathbb E Z_N=O(N)`.
:::

:::theorem "clt_zero_inverse_temperature" (parent := "central_limit_theorem") (uses := "clt_partition_function") (lean := "SYK.CLT.Setting.meanZ_zero, SYK.CLT.Setting.Y_zero, SYK.CLT.Setting.meanLogZ_zero, SYK.CLT.Setting.relativeFluctuation_zero, SYK.CLT.Setting.logFluctuation_zero, SYK.CLT.Setting.varianceZ_zero")
At zero inverse temperature, $`Z_N=\mathbb E Z_N=Y_N=1`. Both real
logarithms and the relative and centered logarithmic fluctuations vanish.
The disorder variance is zero. These identities have Lean proofs without
`sorryAx`; they do not extend the standardized CLT to $`\beta=0`.
:::

:::theorem "clt_log_centering_error" (parent := "central_limit_theorem") (uses := "clt_relative_and_log_moments, clt_second_chaos_and_remainder, clt_gaussian_quadratic_moments") (lean := "SYK.CLT.Setting.cubed_scale_Y_lt_half_bounded, SYK.CLT.Setting.integral_log_Y_isBigO, SYK.CLT.Setting.scaled_sq_Y_lt_half_tendsto_zero, SYK.CLT.Setting.scaled_integral_logLinearError_tendsto_zero, SYK.CLT.Setting.scaled_centered_logLinearError_l1_tendsto_zero")
Write $`W_N=\log Y_N` and $`a=q/2-1`. The active manuscript proof combines
$`\mathbb E(Y_N-1)^2=O(N^{-2a})` with
$`\mathbb P(Y_N<1/2)=O(N^{-3a})`. On the small event,
$`Z_N\ge1` gives $`-\log Y_N\le\log\mathbb E Z_N=O(N)`.
Lean proves $`\mathbb E W_N=O(N^{-2a})`, hence $`o(N^{-a})`, under
`hFE` for each fixed nonzero sufficiently small real $`\beta`, as in
the proof of `thm:free-energy-clt`. The constant may depend on $`\beta`.
This controls the difference
between centering by $`\mathbb E\log Z_N` and by
$`\log\mathbb E Z_N`. Lean proves the required vanishing scaled
mean error and centered $`L^1` error under `hFE`.
:::

:::theorem "log_partition_clt" (parent := "central_limit_theorem") (uses := "partition_function_clt, clt_log_centering_error") (lean := "SYK.CLT.log_partition_clt, SYK.CLT.partition_and_log_partition_clt")
Under the same `hFE`, $`\beta_q`, and real $`0<|\beta|<\beta_q`, the
conclusion is

$$`
N^{q/2-1}\bigl(\log Z_N(\beta)-\mathbb E\log Z_N(\beta)\bigr)
\Longrightarrow
\mathcal N\!\left(0,\frac{q!}{2}\beta^2\ell'(\beta)^2\right).
`

The current manuscript uses the relative CLT, local linearization of
$`\log`, and the preceding centering estimate. Lean verifies the
logarithmic CLT and the joint theorem without `sorryAx`, conditional on
`hFE`. The joint theorem combines the independently proved partition theorem
with the lower-level logarithmic CLT, taking a common smaller positive radius.
The individual logarithmic theorem projects this joint conclusion.
:::

:::theorem "clt_standard_model_application" (parent := "central_limit_theorem") (uses := "partition_function_clt, log_partition_clt") (lean := "SYK.CLT.standardSetting, SYK.CLT.standardSetting_size_iff, SYK.CLT.standardSetting_Z, SYK.CLT.standard_partition_and_log_partition_clt, SYK.CLT.standard_partition_clt, SYK.CLT.standard_log_partition_clt")
`standardSetting` uses the standard Majorana representation at sizes
$`N_n=q+2n`. Every even size at least $`q` occurs exactly once, and
$`N_n` tends to infinity. `standardSetting_Z` identifies the partition
function with the normalized trace in `subsec:SYK-model`.

Assuming `AnnealedInput` for this same family, the joint theorem gives
`thm:partition-clt` and `thm:free-energy-clt` with one common radius,
the manuscript scaling and centering, and positive limiting and
finite-size variances. The two individual theorems are projections of
that result. These are conditional applications: the annealed
proposition and representation independence are not proved here.
:::

:::theorem "clt_expected_pressure_limit" (parent := "central_limit_theorem")
The manuscript's `thm: input` states, for each fixed real $`\beta`, the
deterministic limit of $`N^{-1}\log\mathbb E Z_N(\beta)` and
differentiability of the limiting function on $`\mathbb R`.
The manuscript uses the positive-temperature input from He2026 v3,
Gaussian symmetry, and $`Z_N(0)=1`. The stronger regularity, locally uniform
pressure and derivative convergence, and nonzero-inverse-temperature sign are
stated in `prop:annealed-free-energy`. The current `thm: input` states
neither an expected quenched-pressure limit nor an almost-sure claim.
Lean's conditional CLT assumes the assertions of `prop:annealed-free-energy`
for `S` through `AnnealedInput q S`. The proposition itself remains unproved
in Lean, and no quenched-pressure limit is assumed.
:::
