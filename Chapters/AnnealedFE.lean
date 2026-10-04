import Verso
import VersoManual
import VersoBlueprint
import SYK.Annealed_FE.main_result
import SYK.CLT.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Annealed free energy" =>

:::group "annealed_free_energy"
Two annealed free-energy developments have different models and proof
status. The Rademacher model belongs to
`Annealed_FE/refs/SYK-HT-arxiv.tex`; the Gaussian limit used by the CLT is
an input structure, not a consequence proved from the Rademacher result.
:::

:::definition "gaussian_annealed_input" (parent := "annealed_free_energy") (lean := "SYK.CLT.AnnealedInput")
For one Gaussian model family `S : Setting q`, this structure contains
the convergence, regularity, and sign assertions of
`prop:annealed-free-energy`: an even convex $`C^1` limit on the whole real
line, locally uniform convergence of the normalized pressure and derivative,
and $`\beta\ell_q'(\beta)>0` for nonzero real $`\beta`.

The conditional CLTs receive these assertions as an explicit assumption
for `S`. Constructing an instance for a concrete family is outside the
conditional CLT proof. The current plan defers the proof of the proposition
itself.
:::

:::definition "rademacher_annealed_model" (parent := "annealed_free_energy") (uses := "majorana_system") (lean := "SYK.AnnealedFE.admissibleSize, SYK.AnnealedFE.paperHamiltonian, SYK.AnnealedFE.partitionFunction, SYK.AnnealedFE.annealedPressure")
In the preprint's `eq:anti-commutation` and `eq:H-definition`, the physical
Majorana generators satisfy $`\{\psi_i,\psi_j\}=\delta_{ij}I`, and hence
$`\psi_i^2=I/2`. The $`q`-body Hamiltonian has independent Rademacher
couplings of variance $`(q-1)!/N^{q-1}` and uses
$`Z_{N,q}(\beta)=2^{-N/2}\operatorname{Tr}\exp(\beta H)` for real $`\beta`.
The adapter rescales the shared Majorana operators, adjusts the sign of the
exponential, and takes the normalized trace. It indexes the even-size limit by
$`N=q+2k`.

The existence of the paper-facing canonical Majorana system and several
finite-model identities are still proved with `sorry` in
`SYK.Annealed_FE.main_result`. The definitions compile, but the adapter's
mathematical properties are not yet fully verified.
:::

:::definition "annealed_tree_and_ccg" (parent := "annealed_free_energy") (uses := "rademacher_annealed_model") (lean := "SYK.AnnealedFE.phiC, SYK.AnnealedFE.IsCCG, SYK.AnnealedFE.closedFormulaC")
The preprint's `eq:Phi` defines the complex hypertree series $`\Phi`.
Its CCG fixed-point equation gives the closed expression $`\mathcal F` in
`eq:Phi-is-mathcalF`. Lean contains definitions for both expressions and
their real restrictions. Existence of a canonical CCG, reality of $`\Phi`
on real inputs, and the required equality are not established by complete
proofs; `exists_canonicalCCG` and `phiC_real_of_real` use `sorry`, while
the equality follows from the unfinished threshold specification.
:::

:::theorem "annealed_threshold_and_stationary_point" (parent := "annealed_free_energy") (uses := "annealed_tree_and_ccg") (lean := "SYK.AnnealedFE.exists_betaStar, SYK.AnnealedFE.tStar_mem_Ioo, SYK.AnnealedFE.tStar_stationary")
For each even $`q\ge 2`, the intended threshold $`\beta_*(q)>0` makes
$`\Phi` analytic on $`|z|\le2`, identifies it with the CCG expression,
and selects a unique $`t_*\in(1/2,3/2)` satisfying
$`t_*\Phi'(t_*)=1`; see `prop:t-star` and `prop:t-star-2`.
`exists_betaStar` is a `sorry` proof. The linked stationary-point theorems
unpack that unproved existence statement.
:::

:::theorem "annealed_rademacher_pressure_limit" (parent := "annealed_free_energy") (uses := "rademacher_annealed_model, annealed_threshold_and_stationary_point") (lean := "SYK.AnnealedFE.main_pressure_result, SYK.AnnealedFE.annealed_pressure_limit_closedFormula")
For even $`q\ge2`, a common $`\beta_*(q)>0` is intended to satisfy, for
every real $`|\beta|\le\beta_*(q)`, along $`N=q+2k`,

$$`
\frac{1}{N}\log\mathbb E Z_{N,q}(\beta)
\longrightarrow
\mathcal F^{\mathrm{tot}}_\beta(t_*)-1-\log t_*.
`$$

Here $`\mathcal F^{\mathrm{tot}}_\beta` is the preprint's
$`\mathcal F_\beta` for $`\beta\ne0` and equals $`z` at $`\beta=0`.
This pressure form includes $`\beta=0`. Its Lean proof uses
`exists_betaStar`, whose specification already assumes the pressure limit;
the coefficient asymptotics and saddle-point argument are not formalized.
Consequently this is not a completed kernel-verified limit theorem.
:::

:::theorem "annealed_rademacher_free_energy_limit" (parent := "annealed_free_energy") (uses := "annealed_rademacher_pressure_limit") (lean := "SYK.AnnealedFE.annealed_freeEnergy_density_limit, SYK.AnnealedFE.main_result")
The preprint's `theorem:main-result` states the annealed free-energy density
limit obtained by dividing the preceding pressure limit by $`\beta`.
The Lean statement requires $`\beta\ne0`, since the preprint's displayed
formula is undefined at zero inverse temperature. It retains the even-size limit
and the small real-temperature range. The proof of this wrapper is complete
relative to the pressure statement, but its axioms still include `sorryAx`
from the unfinished upstream construction.
:::
