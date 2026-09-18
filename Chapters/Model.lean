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
Finite-dimensional algebraic and thermodynamic definitions shared by the other
parts of the project.
:::

:::definition "model_parameters" (parent := "model") (lean := "SYK.Params")
The model parameters specify the number of Majorana operators, the interaction
order, and their admissibility conditions. Inverse temperature is passed
separately to analytic and physical constructions.
:::

:::definition "majorana_system" (parent := "model") (lean := "SYK.MajoranaSystem")
A Majorana system is a family of self-adjoint operators satisfying the canonical
anticommutation relations.
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

:::theorem "standard_representation_dimension" (parent := "model") (uses := "standard_representation") (lean := "SYK.standardBasis_card")
The computational basis satisfies $`|D_m|=2^m`. Thus the standard matrix
realization for even $`N` has dimension $`2^{N/2}`.
:::

:::proof "standard_representation_dimension"
The empty tensor product has one basis vector, and each new qubit doubles the
cardinality of the basis.
:::

:::theorem "standard_majorana_relations" (parent := "model") (uses := "standard_representation") (lean := "SYK.jordanWigner_sq, SYK.jordanWigner_self_adjoint, SYK.jordanWigner_anticommute, SYK.jordanWigner_zero, SYK.jordanWigner_succ")
Every Jordan--Wigner generator is self-adjoint and squares to the identity.
Distinct site/type pairs anticommute, so the standard realization obeys

$$`
\psi_i^*=\psi_i,\qquad
\psi_i\psi_j+\psi_j\psi_i=2\delta_{ij}I.
`
:::

:::proof "standard_majorana_relations"
Check the two-by-two Pauli identities directly. Induction on the number of
sites uses $`(A\otimes B)(C\otimes D)=AC\otimes BD` and the adjoint rule
for Kronecker products. At different sites, the X/Y factor at the earlier
site anticommutes with the later generator's parity-string Z factor.
:::

:::theorem "interaction_involutions" (parent := "model") (uses := "majorana_system") (lean := "SYK.MajoranaSystem.majorana_sq, SYK.MajoranaSystem.psiProduct_star_mul_self, SYK.MajoranaSystem.interactionOperator_star, SYK.MajoranaSystem.interactionOperator_sq")
For any complex star-algebra Majorana system and even $`q`, let
$`A=\{a_1<\cdots<a_q\}` and
$`\Psi_A=i^{q/2}\psi_{a_1}\cdots\psi_{a_q}`. Then
$`\Psi_A^*=\Psi_A` and $`\Psi_A^2=I`. For the unphased increasing word $`W_A`, $`W_A^*W_A=I` as well.
These are proved from the abstract relations.
:::

:::proof "interaction_involutions"
The Majorana relation with equal indices gives $`\psi_i^2=I`. Reverse the
word under the adjoint and cancel the pairs of equal generators. The shared
phase has modulus one, and its even-degree adjoint rule gives the square
identity for the phase-corrected interaction.
:::

:::theorem "standard_interaction_orthonormality" (parent := "model") (uses := "standard_representation, partition_function") (lean := "SYK.standardInteraction_orthonormal")
For even $`N` and even $`q`, the shared interaction operators of the standard
representation, indexed by $`q`-element subsets $`A,B`, satisfy

$$`
\operatorname{tr}(\Psi_A^*\Psi_B)=\delta_{A,B},\qquad
\operatorname{tr}(T)=\frac{\operatorname{Tr}(T)}{2^{N/2}}.
`

The increasing order and phase are those of the shared `interactionOperator`.
Orthogonality is a proved conclusion, with no extra field in `MajoranaSystem`.
:::

:::proof "standard_interaction_orthonormality" (uses := "standard_majorana_relations, interaction_involutions")
If $`A=B`, the square identity and $`\operatorname{tr}(I)=1` give one.
Otherwise equal cardinalities provide $`i\in A\setminus B`. At even degree,
$`\Psi_A` anticommutes with $`\psi_i` and $`\Psi_B` commutes with it.
Conjugation by $`\psi_i` therefore changes the sign of $`\Psi_A\Psi_B`,
while cyclicity of the finite matrix trace leaves its trace unchanged.
The trace is zero. This fixed-degree argument uses the Majorana relations and
cyclicity; it does not require a separate irreducibility assumption.
:::

:::definition "interaction_hamiltonian" (parent := "model") (lean := "SYK.hamiltonian")
The finite-dimensional Hamiltonian is the prescribed linear combination of
ordered Majorana interaction operators.
:::

:::definition "scaled_syk_hamiltonian" (parent := "model") (uses := "interaction_hamiltonian") (lean := "SYK.CouplingSpace, SYK.standardGaussianMeasure, SYK.couplingScale, SYK.normalizedHamiltonian")
For valid parameters $`(N,q)` and a finite matrix Majorana system, let
$`g=(g_A)_{|A|=q}` be standard Gaussian coordinates and define

$$`
\sigma_N=\sqrt{\frac{(q-1)!}{N^{q-1}}},
\qquad J_A=\sigma_N g_A,
\qquad H(g)=\sum_{|A|=q}J_A\Psi_A.
`

Here $`\Psi_A=i^{q/2}\psi_{a_1}\cdots\psi_{a_q}` uses increasing labels.
Under the product standard Gaussian measure, the actual coefficients $`J_A`
are independent centered Gaussians, each with variance
$`\sigma_N^2=(q-1)!/N^{q-1}`. This is the variance of one coefficient,
not of the whole Hamiltonian. Concentration estimates use the Euclidean norm
of $`g`, rather than the actual coefficient vector $`J`.
This matches the lecture notes at `eq:Hqnormalized` and `eq:Jcovariance`,
and the CLT manuscript at `subsec:SYK-model`; the shared construction does not
impose the manuscript's additional $`q\ge4` or standard representation.
:::

:::theorem "standard_hamiltonian_properties" (parent := "model") (uses := "scaled_syk_hamiltonian") (lean := "SYK.couplingScale_nonneg, SYK.couplingScale_sq, SYK.normalizedHamiltonian_zero, SYK.normalizedHamiltonian_add, SYK.normalizedHamiltonian_smul, SYK.normalizedHamiltonian_affine, SYK.normalizedHamiltonian_self_adjoint")
The standard scale is nonnegative and its square is $`(q-1)!/N^{q-1}`.
The Hamiltonian is real linear in the Gaussian coordinates and self-adjoint:

$$`
H(g+s v)=H(g)+sH(v),\qquad H(g)^*=H(g)
\quad(s\in\mathbb R).
`
:::

:::proof "standard_hamiltonian_properties"
The square identity follows from nonnegativity of the variance and the real
square-root identity. Linearity follows by expanding the finite sum; real
coefficients and self-adjoint interaction operators give self-adjointness.
:::

:::definition "partition_function" (parent := "model") (lean := "SYK.partitionFunction")
The partition function accepts complex inverse temperature and uses the
matrix trace of the Gibbs operator. Its value at zero inverse temperature is
the dimension of the matrix index type. The separately named normalized trace
is available when a dimension-normalized quantity is needed.
:::

:::theorem "partition_function_complex_derivative" (parent := "model") (uses := "partition_function") (lean := "SYK.partitionFunction_has_deriv_at")
For every finite-dimensional complex matrix $`H` and every $`z \in \mathbb{C}`,
the partition function $`Z_H(z) = \operatorname{Tr}(\exp(-zH))` has complex
derivative
$$`Z_H'(z) = -\operatorname{Tr}(H\exp(-zH)).`
No self-adjointness or nonvanishing assumption is used.
:::

:::theorem "partition_function_analytic" (parent := "model") (uses := "partition_function_complex_derivative") (lean := "SYK.partitionFunction_differentiable, SYK.partitionFunction_analytic_at")
The same partition function is complex differentiable and analytic at every
$`z \in \mathbb{C}`. This records entire analyticity pointwise; it does not
assert that the partition function has no zeros.
:::

:::theorem "partition_function_log_derivative" (parent := "model") (uses := "partition_function_complex_derivative") (lean := "SYK.partitionFunction_mul_log_deriv")
At a point $`z` satisfying $`Z_H(z) \ne 0`, the logarithmic derivative obeys
$$`Z_H(z)\,\operatorname{logDeriv}(Z_H)(z)
= -\operatorname{Tr}(H\exp(-zH)).`
This is a pointwise quotient formula. It neither constructs a zero-free region
nor chooses a branch of the complex logarithm.
:::
