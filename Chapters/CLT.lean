import Verso
import VersoManual
import VersoBlueprint
import SYK.CLT.Main
import SYK.CLT.Lemmas.ConvexDerivatives
import SYK.CLT.Lemmas.GaussianIBP

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
Given `hFE : AnnealedInput q`, Lean proves convergence of the annealed
pressure and its derivative, and the second-chaos coefficient limit, for
$`|\beta|<hFE.\beta_{FE}`. The same assumption supplies a common analytic
limit and locally uniform convergence for every `Setting q`. These results
are proved conditional statements; neither the Rademacher theorem above
nor the CLT manuscript's `prop:annealed-free-energy` constructs `hFE`.
The latter states an even convex $`C^1` limit on all of $`\mathbb R` and
derives explicit small-temperature bounds from He2026.
:::

:::theorem "clt_convex_derivative_transfer" (parent := "central_limit_theorem") (lean := "SYK.CLT.convex_convergence_deriv_tendstoUniformlyOn")
The Lean convexity lemma gives locally uniform convergence of derivatives
when locally uniform convergence of differentiable convex functions to a
$`C^1` limit is already known. The manuscript's `lem:convex-derivatives`
also derives locally uniform convergence of the functions from pointwise
convergence. That first step remains separate from the linked Lean result.
:::

:::theorem "clt_conditional_nondegeneracy" (parent := "central_limit_theorem") (uses := "clt_conditional_annealed_limit") (lean := "SYK.CLT.exists_small_temperature_sign, SYK.CLT.exists_small_temperature_variance_pos")
The derivative expansion in `hFE` gives
$`\beta\ell'(\beta)>0` and a positive limiting variance at sufficiently
small nonzero real $`\beta`. These are verified conditional Lean results.
They do not imply positive variance at every finite size.
:::

:::theorem "clt_gaussian_hermite_ibp" (parent := "central_limit_theorem") (lean := "SYK.CLT.GaussianIBP.hermiteMulti_ibp_of_expGrowth, SYK.CLT.GaussianIBP.hermiteMulti_ibp_integrable, SYK.CLT.GaussianIBP.hermiteMulti_eq_prod, SYK.CLT.GaussianIBP.partialList_perm")
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

The manuscript's final specialization to $`Z_N` remains assigned to F04:
its smoothness and derivative growth estimates are separate unfinished
inputs. Completeness of the Hermite expansion and chaos projections are
also separate results.
:::

:::theorem "clt_second_chaos_and_remainder" (parent := "central_limit_theorem") (uses := "clt_partition_moments, clt_conditional_annealed_limit, clt_gaussian_hermite_ibp")
The manuscript's `lem:exact-second-chaos` identifies the leading Gaussian
chaos of $`Y_N-1`. Its `prop:higher-chaos-closure` bounds the remainder by
$`\|\mathcal R_N\|_2^2=O(N^{-3a})`, where $`a=q/2-1`.
The intended proof uses parity symmetry, Gaussian integration by parts,
Duhamel derivatives, and Rademacher encoding of the higher-chaos sum.
The general integration-by-parts input is proved above; the application
to the partition function and these chaos conclusions remain unfinished.
:::

:::theorem "partition_function_clt" (parent := "central_limit_theorem") (uses := "clt_second_chaos_and_remainder, clt_conditional_nondegeneracy") (lean := "SYK.CLT.partition_clt, SYK.CLT.partition_and_log_partition_clt")
Assume `hFE : AnnealedInput q`. The Lean statements choose
$`0<\beta_q\le hFE.\beta_{FE}` so that, for every `Setting q` and real
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
