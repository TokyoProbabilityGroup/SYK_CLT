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
order, and their admissibility conditions. The current Lean declaration also
contains an inverse temperature; the planned shared API will pass inverse
temperature separately.
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
The current partition function is the matrix trace of the Gibbs operator. The
planned API will distinguish the raw trace from the normalized trace and will
also accept complex inverse temperature for analytic results.
:::
