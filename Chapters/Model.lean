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
