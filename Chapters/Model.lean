import Verso
import VersoManual
import VersoBlueprint
import SYK.Model.FiniteDimensionalGibbs
import SYK.Model.Majorana

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

:::definition "interaction_hamiltonian" (parent := "model") (lean := "SYK.hamiltonian")
The finite-dimensional Hamiltonian is the prescribed linear combination of
ordered Majorana interaction operators.
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
