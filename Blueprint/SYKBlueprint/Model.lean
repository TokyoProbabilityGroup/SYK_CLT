import Verso
import VersoManual
import VersoBlueprint
import SYK.Model.FiniteDimensionalGibbs
import SYK.Model.Majorana
import SYK.Model.GaussianDisorder
import SYK.Model.StandardRepresentation

set_option linter.mathlibStandardSet false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Finite-dimensional SYK model" =>

:::group "model"
Finite-dimensional SYK model
:::

:::definition "model_parameters" (parent := "model") (lean := "SYK.Params")
The shared finite model has integers $`N,q` satisfying
$`0<q\le N` and $`q` even, hence $`N>0` and $`q\ge2`.
It does not require $`N` even. The CLT manuscript's `subsec:SYK-model`
additionally requires even $`N` and $`q\ge4`.
Inverse temperature is a separate argument.
:::

:::definition "majorana_system" (parent := "model") (lean := "SYK.MajoranaSystem")
A Majorana system consists of self-adjoint operators with
$$`
\psi_i^*=\psi_i,\qquad
\psi_i\psi_j+\psi_j\psi_i=2\delta_{ij}I.
`
In particular, $`\psi_i^2=I`, and distinct generators anticommute.
:::

:::definition "standard_representation" (parent := "model") (uses := "majorana_system") (lean := "SYK.StandardBasis, SYK.jordanWignerPauli, SYK.jordanWignerZ, SYK.jordanWigner, SYK.jordanWignerSystem, SYK.standardMajoranaSystem")
For $`m` qubits, the computational basis is defined recursively by
$`D_0=\{\ast\}` and $`D_{m+1}=\{0,1\}\times D_m`.
Let $`X,Y,Z` be the Pauli matrices, with

$$`
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}.
`

With zero-based site labels $`0\le a<m`, the Jordan--Wigner generators are

$$`
\psi_{2a}=Z^{\otimes a}\otimes X\otimes I^{\otimes(m-a-1)},\qquad
\psi_{2a+1}=Z^{\otimes a}\otimes Y\otimes I^{\otimes(m-a-1)}.
`

The implementation uses Kronecker products with the first site outermost.
The zero-based label $`j` corresponds to label $`j+1` in the lecture notes'
Jordan--Wigner subsection and `eq:majoranaCAR`. For even $`N`, setting
$`m=N/2` gives a matrix realization with exactly $`N` generators.
The same representation and trace normalization are used in the CLT manuscript
at `subsec:SYK-model`.
:::

:::theorem "standard_representation_dimension" (parent := "model") (lean := "SYK.standardBasis_card")
The computational basis satisfies $`|D_m|=2^m`. Thus the standard matrix
realization for even $`N` has dimension $`2^{N/2}`.
:::

:::proof "standard_representation_dimension" (uses := "standard_representation")
The empty tensor product has one basis vector, and each new qubit doubles the
cardinality of the basis.
:::

:::theorem "standard_majorana_relations" (parent := "model") (lean := "SYK.jordanWigner_sq, SYK.jordanWigner_self_adjoint, SYK.jordanWigner_anticommute")
Every Jordan--Wigner generator is self-adjoint and squares to the identity.
Distinct site/type pairs anticommute, so the standard realization obeys

$$`
\psi_i^*=\psi_i,\qquad
\psi_i\psi_j+\psi_j\psi_i=2\delta_{ij}I.
`
:::

:::proof "standard_majorana_relations" (uses := "standard_representation")
Check the two-by-two Pauli identities directly. Induction on the number of
sites uses $`(A\otimes B)(C\otimes D)=AC\otimes BD` and the adjoint rule
for Kronecker products. At different sites, the X/Y factor at the earlier
site anticommutes with the later generator's parity-string Z factor.
:::

:::theorem "interaction_involutions" (parent := "model") (lean := "SYK.MajoranaSystem.majorana_sq, SYK.MajoranaSystem.psiProduct_star_mul_self, SYK.MajoranaSystem.interactionOperator_star, SYK.MajoranaSystem.interactionOperator_sq")
For any complex star-algebra Majorana system and even $`q`, let
$`I=\{i_1<\cdots<i_q\}` and
$`\psi_I=i^{q/2}\psi_{i_1}\cdots\psi_{i_q}`. Then
$`\psi_I^*=\psi_I` and $`\psi_I^2=I`. For the unphased increasing word $`W_I`, $`W_I^*W_I=I` as well.
:::

:::proof "interaction_involutions" (uses := "majorana_system")
The Majorana relation with equal indices gives $`\psi_i^2=I`. Reverse the
word under the adjoint and cancel the pairs of equal generators. The shared
phase has modulus one, and its even-degree adjoint rule gives the square
identity for the phase-corrected interaction.
:::

:::definition "interaction_hamiltonian" (parent := "model") (lean := "SYK.hamiltonian")
For $`I=\{i_1<\cdots<i_q\}`, set
$`\psi_I=\mathrm i^{q/2}\psi_{i_1}\cdots\psi_{i_q}`.
For real coefficients $`J_I`, the finite Hamiltonian is
$$`
H=\sum_{I:\,|I|=q}J_I\psi_I.
`
:::

:::definition "scaled_syk_hamiltonian" (parent := "model") (uses := "interaction_hamiltonian") (lean := "SYK.CouplingSpace, SYK.standardGaussianMeasure, SYK.couplingScale, SYK.normalizedHamiltonian")
For valid parameters $`(N,q)` and a finite matrix Majorana system, let
$`g=(g_I)_{|I|=q}` be standard Gaussian coordinates and define

$$`
\sigma_N=\sqrt{\frac{(q-1)!}{N^{q-1}}},
\qquad J_I=\sigma_N g_I,
\qquad H(g)=\sum_{|I|=q}J_I\psi_I.
`

Here $`\psi_I=i^{q/2}\psi_{i_1}\cdots\psi_{i_q}` uses increasing labels.
Under the product standard Gaussian measure, the actual coefficients $`J_I`
are independent centered Gaussians, each with variance
$`\sigma_N^2=(q-1)!/N^{q-1}`. This is the variance of one coefficient,
not of the whole Hamiltonian. Concentration estimates use the Euclidean norm
of $`g`, rather than the actual coefficient vector $`J`.
This matches the lecture notes at `eq:Hqnormalized` and `eq:Jcovariance`,
and the CLT manuscript at `subsec:SYK-model`; the shared construction does not
impose the manuscript's additional $`q\ge4` or standard representation.
:::

:::theorem "standard_hamiltonian_properties" (parent := "model") (lean := "SYK.couplingScale_nonneg, SYK.couplingScale_sq, SYK.normalizedHamiltonian_zero, SYK.normalizedHamiltonian_add, SYK.normalizedHamiltonian_smul, SYK.normalizedHamiltonian_affine, SYK.normalizedHamiltonian_self_adjoint")
The standard scale is nonnegative and its square is $`(q-1)!/N^{q-1}`.
The Hamiltonian is real linear in the Gaussian coordinates and self-adjoint:

$$`
H(g+s v)=H(g)+sH(v),\qquad H(g)^*=H(g)
\quad(s\in\mathbb R).
`
:::

:::proof "standard_hamiltonian_properties" (uses := "scaled_syk_hamiltonian")
The square identity follows from nonnegativity of the variance and the real
square-root identity. Linearity follows by expanding the finite sum; real
coefficients and self-adjoint interaction operators give self-adjointness.
:::

:::definition "partition_function" (parent := "model") (lean := "SYK.partitionFunction")
For a finite complex matrix $`H` and complex inverse temperature $`z`,
the ordinary partition function is
$$`
Z_H(z)=\operatorname{Tr}e^{-zH},\qquad Z_H(0)=d.
`
Here $`d` is the matrix dimension. The dimension-normalized quantity is
$`d^{-1}Z_H` for $`d>0`; the CLT uses this normalization.
:::

:::theorem "partition_function_complex_derivative" (parent := "model") (lean := "SYK.partitionFunction_has_deriv_at")
For every finite-dimensional complex matrix $`H` and every $`z \in \mathbb{C}`,
the partition function $`Z_H(z) = \operatorname{Tr}(\exp(-zH))` has complex
derivative
$$`Z_H'(z) = -\operatorname{Tr}(H\exp(-zH)).`
No self-adjointness or nonvanishing assumption is used.
:::

:::proof "partition_function_complex_derivative" (uses := "partition_function")
Differentiate the matrix-exponential power series under the trace.
Cyclicity identifies the sum with $`-\operatorname{Tr}(He^{-zH})`.
:::

:::theorem "partition_function_analytic" (parent := "model") (lean := "SYK.partitionFunction_differentiable, SYK.partitionFunction_analytic_at")
The same partition function is complex differentiable and analytic at every
$`z \in \mathbb{C}`. This records entire analyticity pointwise; it does not
assert that the partition function has no zeros.
:::

:::proof "partition_function_analytic" (uses := "partition_function_complex_derivative")
The matrix exponential is entire and trace is continuous linear.
Composition with $`z\mapsto-zH` preserves analyticity.
:::

:::theorem "partition_function_log_derivative" (parent := "model") (lean := "SYK.partitionFunction_mul_log_deriv")
At a point $`z` satisfying $`Z_H(z) \ne 0`, the logarithmic derivative obeys
$$`Z_H(z)\,\operatorname{logDeriv}(Z_H)(z)
= -\operatorname{Tr}(H\exp(-zH)).`
This is a pointwise quotient formula. It neither constructs a zero-free region
nor chooses a branch of the complex logarithm.
:::

:::proof "partition_function_log_derivative" (uses := "partition_function_complex_derivative")
Use the derivative formula and the definition of the logarithmic derivative
at a point where the partition function is nonzero.
:::

:::theorem "partition_function_local_zero_free" (parent := "model") (lean := "SYK.partitionFunction_re_pos_real, SYK.partitionFunction_re_pos_near_real, SYK.partitionFunction_ne_zero_near_real, SYK.partitionFunction_mul_log_deriv_near_real, SYK.partitionFunction_log_differentiable_near_real")
Fix a nonempty finite-dimensional matrix space and a Hermitian matrix $`H`.
For every real inverse temperature $`\beta`, there is a radius
$`\varepsilon(H,\beta)>0` such that
$`\operatorname{Re}Z_H(z)>0` whenever $`|z-\beta|<\varepsilon(H,\beta)`.
This supplies $`Z_H(z)\ne0` to the pointwise logarithmic-derivative formula.
The principal complex logarithm $`\log Z_H` is holomorphic on the same disk,
because its values lie in the right half-plane. The radius need not be
uniform in $`H`, matrix dimension, or disorder realization; no such
uniformity is used by the current real inverse-temperature CLT.
:::

:::proof "partition_function_local_zero_free" (uses := "partition_function_analytic, partition_function_log_derivative")
At real $`\beta`, diagonalization gives a positive real trace.
Continuity preserves its positive real part on a sufficiently small disk.
The principal logarithm is holomorphic on the right half-plane, so composition
gives the local logarithm and its derivative.
:::
