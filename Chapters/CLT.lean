import Verso
import VersoManual
import VersoBlueprint
import SYK.CLT.Main
import SYK.CLT.Lemmas.ConvexDerivatives
import SYK.CLT.Lemmas.GaussianIBP
import SYK.CLT.Lemmas.GaussianChaos
import SYK.CLT.Lemmas.GaussianHermiteOrthogonality
import SYK.CLT.Lemmas.GaussianHermiteDensity
import SYK.CLT.Lemmas.GaussianPolynomialDensity
import SYK.CLT.Lemmas.CLTComponents

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Central limit theorem" =>

:::group "central_limit_theorem"
Gaussian SYK partition-function and log-partition fluctuations at fixed even
$`q\ge4`. The manuscript is `CLT/refs/CLT_SYK.tex` with its four included
sections. The active log-CLT proof is in `main-results.tex`; the argument
inside `\iffalse` is historical.

Finite-model results, conditional consequences of an external annealed input,
and unfinished CLT proofs have different status below.
:::

:::definition "clt_partition_function" (parent := "central_limit_theorem") (uses := "scaled_syk_hamiltonian") (lean := "SYK.CLT.partitionFunction, SYK.CLT.realPartitionFunction, SYK.CLT.Setting")
Fix even $`q\ge4`. For each even $`N\ge q`, choose a nonempty finite
matrix Majorana representation of dimension $`d_N`. The Gaussian coordinates
$`g_I` are independent and standard normal, and

$$`
H_N(g)=\sigma_N\sum_{|I|=q}g_I\Psi_I,
\qquad \sigma_N^2=\frac{(q-1)!}{N^{q-1}},
\qquad Z_N(z;g)=\frac{1}{d_N}\operatorname{Tr}\exp(-zH_N(g)).
`$$

For real $`\beta`, Lean uses the real part of $`Z_N(\beta;g)` to define
$`Y_N=Z_N/\mathbb E Z_N` and its fluctuations. `Setting q` allows any
diverging sequence of even sizes and a separate Gaussian coupling space at
each size. The manuscript's `subsec:SYK-model` uses the standard
$`d_N=2^{N/2}` representation; the general-family external limit has not
been supplied.
:::

:::theorem "clt_finite_partition_properties" (parent := "central_limit_theorem") (uses := "clt_partition_function") (lean := "SYK.CLT.partitionFunction_zero, SYK.CLT.partitionFunction_eq_trace_div_card, SYK.CLT.partitionFunction_im_eq_zero, SYK.CLT.realPartitionFunction_pos, SYK.CLT.partitionFunction_standard")
The normalized partition function satisfies $`Z_N(0;g)=1`, agrees with the
shared ordinary-trace partition function after division by $`d_N`, and is
real and strictly positive at every real inverse temperature. These
finite-dimensional statements have Lean proofs without `sorryAx`.
Specialization to the standard representation gives the coefficient
$`(2^{N/2})^{-1}` by `standardBasis_card`; no representation-independence
claim is needed.
:::

:::theorem "clt_partition_moments" (parent := "central_limit_theorem") (uses := "clt_trace_lower_bound") (lean := "SYK.CLT.Setting.partition_moments")
For each real $`\beta` and size, $`Z_N\in L^2`, $`\log Z_N` is
integrable, and $`\mathbb E Z_N>0`. These Lean proofs have no `sorryAx`
and need no annealed input. The Hamiltonian is a continuous linear map
of the finite-dimensional Gaussian coordinates, so
$`Z_N(\beta;g)\le\exp(C\|g\|)` for a finite nonnegative constant
depending on the model and temperature. Gaussian exponential
integrability controls the square, while $`1\le Z_N` bounds the
logarithm between zero and $`C\|g\|`.
:::

:::theorem "clt_conditional_annealed_limit" (parent := "central_limit_theorem") (uses := "gaussian_annealed_input") (lean := "SYK.CLT.annealedFreeEnergy_tendsto, SYK.CLT.annealedDerivative_tendsto, SYK.CLT.secondChaosCoefficient_tendsto")
Given `S : Setting q` and `hFE : AnnealedInput q S`, Lean proves convergence
of the annealed pressure and its derivative, and the second-chaos
coefficient limit, for every real $`\beta`. The input records the even,
convex $`C^1` limit and bounds of manuscript Proposition 4.2 for this
one family. Constructing `hFE` from the manuscript remains separate.
:::

:::theorem "clt_convex_derivative_transfer" (parent := "central_limit_theorem") (lean := "SYK.CLT.convex_convergence_deriv_tendstoUniformlyOn")
The Lean convexity lemma gives locally uniform convergence of derivatives
when locally uniform convergence of differentiable convex functions to a
$`C^1` limit is already known. The manuscript's `lem:convex-derivatives`
also derives locally uniform convergence of the functions from pointwise
convergence. That first step remains separate from the linked Lean result.
:::

:::theorem "clt_conditional_nondegeneracy" (parent := "central_limit_theorem") (uses := "clt_conditional_annealed_limit") (lean := "SYK.CLT.exists_small_temperature_sign, SYK.CLT.exists_small_temperature_variance_pos")
The sign field in `hFE` gives
$`\beta\ell'(\beta)>0` for every nonzero real $`\beta`, and hence positive
limiting variance. These are verified conditional Lean results.
They do not imply positive variance at every finite size.
:::

:::theorem "clt_gaussian_hermite_ibp" (parent := "central_limit_theorem") (lean := "SYK.GaussianConcentration.hermiteMulti_ibp_of_expGrowth, SYK.GaussianConcentration.hermiteMulti_ibp_integrable, SYK.GaussianConcentration.hermiteMulti_pair_ibp, SYK.GaussianConcentration.hermiteMulti_eq_prod, SYK.GaussianConcentration.partialList_perm, SYK.CLT.hermite_coefficient_ibp, SYK.CLT.integral_hermiteMulti_eq_zero")
The general identity in `lem:Gaussian-Hermite-IBP` is proved for any finite
coordinate set and independent standard Gaussian coordinates. Let
$`\alpha` be a nonnegative integer multi-index and let
$`f\in C^{|\alpha|}(\mathbb R^\iota;\mathbb R)`. For each
$`\eta\le\alpha` componentwise, assume there is $`C_\eta>0` such that
$`|\partial^\eta f(g)|\le C_\eta\exp(C_\eta\|g\|_2)` for every $`g`.
Then both expectations below are integrable and

$$`
\mathbb E\left[\left(\prod_{i\in\iota}\operatorname{He}_{\alpha_i}(G_i)\right)
f(G)\right]=\mathbb E[\partial^\alpha f(G)].
`$$

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

The manuscript's final specialization to $`Z_N` remains assigned to F04:
its smoothness and derivative growth estimates are separate unfinished
inputs.
:::

:::theorem "clt_hermite_polynomial_span" (parent := "central_limit_theorem") (lean := "SYK.CLT.realHermiteBasis, SYK.CLT.polynomialProdEval_mem_hermiteMulti_span, SYK.CLT.mvPolynomial_eval_mem_hermiteMulti_span, SYK.CLT.mvPolynomial_eval_memLp_and_hermiteSpan, SYK.CLT.hermiteOrthonormal_dense_of_mvPolynomialLp_dense")
For a finite coordinate set, every real multivariate polynomial function is
a finite real linear combination of products of probabilists' Hermite
polynomials. Lean proves this first for a product of one-variable
polynomials, then for arbitrary multivariate polynomials by induction on
monomials. The polynomial functions define Gaussian $`L^2` classes in the
span of the Hermite classes. Polynomial density and unconditional
Hermite completeness are proved in the node below.
:::

:::theorem "clt_exponential_moment_determination" (parent := "central_limit_theorem") (lean := "SYK.CLT.measure_eq_of_moments, SYK.CLT.gaussianExp_memLp_two, SYK.CLT.gaussianLp_integrable_mul_exp")
Finite real measures with every real exponential moment are determined by
their polynomial moments. Lean proves this through the analytic moment
generating function and characteristic-function uniqueness. Real
exponentials belong to standard Gaussian $`L^2`, and their products with
arbitrary Gaussian $`L^2` functions are integrable. Applying moment
determination to every linear projection proves polynomial density below.
:::

:::theorem "clt_finite_hermite_projection" (parent := "central_limit_theorem") (uses := "clt_gaussian_hermite_ibp") (lean := "SYK.CLT.hermiteMulti_orthogonality, SYK.CLT.inner_hermiteLp, SYK.CLT.hermiteFiniteProjection_eq_starProjection, SYK.CLT.mem_multiIndices_degree, SYK.CLT.hermiteOrthonormal_orthonormal, SYK.CLT.hasSum_hermiteDegreeProjection")
For every finite set of standard Gaussian coordinates, the probabilists'
Hermite products satisfy

$$`
\mathbb E[H_\alpha(G)H_\eta(G)]
=\mathbf1_{\{\alpha=\eta\}}\prod_i\alpha_i!.
`$$

For any finite set $`S` of multi-indices and real $`f\in L^2(\gamma)`, the
orthogonal projection onto $`\operatorname{span}\{H_\alpha:\alpha\in S\}`
is the finite coefficient sum

$$`
\sum_{\alpha\in S}
\frac{\langle H_\alpha,f\rangle}{\prod_i\alpha_i!}H_\alpha.
`$$

The set $`\{\alpha:|\alpha|=r\}` is finite, so this applies to each
homogeneous degree. Normalizing each Hermite product by its $`L^2` norm
gives a checked orthonormal family. Under the explicit assumption that its
span is dense in Gaussian $`L^2`, Lean proves that the infinite sum of
degree projections converges to $`f` in $`L^2`. The required density
is supplied by the next node. The linked Lean declarations have no
`sorryAx`.
:::

:::theorem "clt_hermite_complete" (parent := "central_limit_theorem") (uses := "clt_hermite_polynomial_span, clt_exponential_moment_determination, clt_finite_hermite_projection") (lean := "SYK.CLT.gaussianMonomialLp_dense, SYK.CLT.mvPolynomialLp_dense, SYK.CLT.hermiteOrthonormal_dense, SYK.CLT.hasSum_hermiteCoefficients_unconditional, SYK.CLT.hasSum_hermiteDegreeProjection_unconditional")
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
the manuscript's `lem:exact-second-chaos` holds in Gaussian $`L^2`:
$`P_1Y_N=0` and
$`P_2Y_N=\frac{\beta\partial_\beta\log\mathbb E Z_N}{2M_N}\sum_I(g_I^2-1)`.
The normalization is $`M_N=\binom Nq`, with $`H_2(x)=x^2-1`
and $`\mathbb E H_2(g_I)^2=2`.
:::

:::proof "clt_exact_second_chaos" (uses := "clt_partition_moments, clt_gaussian_hermite_ibp")
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

:::theorem "clt_second_chaos_and_remainder" (parent := "central_limit_theorem") (uses := "clt_exact_second_chaos, clt_gaussian_hermite_ibp")
The manuscript's `lem:exact-second-chaos` identifies the leading Gaussian
chaos of $`Y_N-1`. Its `prop:higher-chaos-closure` bounds the remainder by
$`\|\mathcal R_N\|_2^2=O(N^{-3a})`, where $`a=q/2-1`.
The intended proof uses parity symmetry, Gaussian integration by parts,
Duhamel derivatives, and Rademacher encoding of the higher-chaos sum.
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
theorem above. The higher-chaos remainder bound remains unfinished;
it requires the higher-order partition derivative estimates and the
Rademacher encoding and moment bounds.
:::

:::theorem "partition_function_clt" (parent := "central_limit_theorem") (uses := "clt_second_chaos_and_remainder, clt_conditional_nondegeneracy") (lean := "SYK.CLT.partition_clt, SYK.CLT.partition_and_log_partition_clt")
Assume `S : Setting q` and `hFE : AnnealedInput q S`. The Lean statements
choose $`0<\beta_q` so that, for real
$`|\beta|<\beta_q`, the annealed pressure converges to $`\ell(\beta)` and

$$`
N^{q/2-1}(Y_N(\beta)-1)
\Longrightarrow
\mathcal N\!\left(0,\frac{q!}{2}\beta^2\ell'(\beta)^2\right).
`$$

For $`\beta\ne0`, the statements also require positive limiting variance,
positive variance at every finite size, and a standardized CLT. At
$`\beta=0`, the relative limit is degenerate and standardization is excluded.
The joint declaration and its two projections depend on `sorryAx`.
The manuscript's `thm:partition-clt` includes zero in its standardized
formula; its parameter range still needs correction before treating the
manuscript and Lean statements as identical.
:::

:::theorem "clt_trace_lower_bound" (parent := "central_limit_theorem") (uses := "clt_finite_partition_properties") (lean := "SYK.CLT.interactionOperator_trace_eq_zero, SYK.CLT.normalizedHamiltonian_normalizedTrace_eq_zero, SYK.CLT.realPartitionFunction_ge_one")
In the active proof of `cor:free-energy-clt`, conjugation by a Majorana
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
`$$

Moreover, $`\log Z_N\ge0`, $`\log\mathbb E Z_N\ge0`, and
$`-\log Y_N\le\log\mathbb E Z_N`. These finite-model inputs to
`cor:free-energy-clt` are proved without `sorryAx`. They do not supply
the asymptotic estimate $`\log\mathbb E Z_N=O(N)`.
:::

:::theorem "clt_zero_inverse_temperature" (parent := "central_limit_theorem") (uses := "clt_partition_function") (lean := "SYK.CLT.Setting.meanZ_zero, SYK.CLT.Setting.Y_zero, SYK.CLT.Setting.meanLogZ_zero, SYK.CLT.Setting.relativeFluctuation_zero, SYK.CLT.Setting.logFluctuation_zero, SYK.CLT.Setting.varianceZ_zero")
At zero inverse temperature, $`Z_N=\mathbb E Z_N=Y_N=1`. Both real
logarithms and the relative and centered logarithmic fluctuations vanish.
The disorder variance is zero. These identities have Lean proofs without
`sorryAx`; they do not extend the standardized CLT to $`\beta=0`.
:::

:::theorem "clt_log_centering_error" (parent := "central_limit_theorem") (uses := "clt_relative_and_log_moments, clt_second_chaos_and_remainder")
Write $`W_N=\log Y_N` and $`a=q/2-1`. The active manuscript proof combines
$`\mathbb E(Y_N-1)^2=O(N^{-2a})` with
$`\mathbb P(Y_N<1/2)=O(N^{-3a})`. On the small event,
$`Z_N\ge1` gives $`-\log Y_N\le\log\mathbb E Z_N=O(N)`.
It follows that $`\mathbb E W_N=o(N^{-a})`, which controls the difference
between centering by $`\mathbb E\log Z_N` and by
$`\log\mathbb E Z_N`. This estimate is not formalized in Lean.
:::

:::theorem "log_partition_clt" (parent := "central_limit_theorem") (uses := "partition_function_clt, clt_log_centering_error") (lean := "SYK.CLT.log_partition_clt, SYK.CLT.partition_and_log_partition_clt")
Under the same `hFE`, $`\beta_q`, and real $`|\beta|<\beta_q`, the intended
conclusion is

$$`
N^{q/2-1}\bigl(\log Z_N(\beta)-\mathbb E\log Z_N(\beta)\bigr)
\Longrightarrow
\mathcal N\!\left(0,\frac{q!}{2}\beta^2\ell'(\beta)^2\right).
`$$

The current manuscript uses the relative CLT, local linearization of
$`\log`, and the preceding centering estimate. The Lean joint theorem has
a `sorry` proof; its log-CLT projection therefore has `sorryAx` as well.
:::

:::theorem "free_energy_law_of_large_numbers" (parent := "central_limit_theorem")
The manuscript's `thm: input` attributes an almost-sure fixed-temperature
limit of $`N^{-1}\log Z_N` and the annealed pressure limit for every real
$`\beta` to He2026. He2026 Theorem 1.1 directly states limits of
expected quenched and annealed pressures at fixed positive temperature.
The almost-sure upgrade, extension to negative temperature, and the
applicability to Lean's general representation families require separate
justification. No Lean theorem in this project supplies this input.
:::
