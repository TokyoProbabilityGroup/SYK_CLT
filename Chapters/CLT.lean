import Verso
import VersoManual
import VersoBlueprint
import SYK.CLT.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Central limit theorem" =>

:::group "central_limit_theorem"
The asymptotic results for the partition function and its logarithm at fixed
even interaction order.

The declarations in `SYK.CLT.Main` currently use authorized `sorry` proof
placeholders. The statements below describe the intended mathematics and
are not completed formal proofs. The manuscript sources are `subsec:SYK-model`,
`thm:partition-clt`, and `cor:free-energy-clt`.
:::

:::definition "clt_partition_function" (parent := "central_limit_theorem") (uses := "scaled_syk_hamiltonian") (lean := "SYK.CLT.partitionFunction, SYK.CLT.Setting")
Fix an even integer $`q\geq4`. For each even $`N\geq q`, choose a general
Majorana system on a nonempty finite-dimensional matrix space of dimension
$`d_N`, satisfying $`\psi_i\psi_j+\psi_j\psi_i=2\delta_{ij}I` and
$`\psi_i^*=\psi_i`. Use the shared Gaussian Hamiltonian
$`H_N=\sigma_N\sum_I g_I\psi_I`, with independent standard Gaussian
coordinates and $`\sigma_N^2=(q-1)!/N^{q-1}`. Define

$$`
Z_N(z;g)=d_N^{-1}\operatorname{Tr}\exp(-zH_N(g)),
\qquad Y_N(\beta;g)=\frac{Z_N(\beta;g)}{\mathbb E Z_N(\beta)}.
`$$

In the standard representation $`d_N=2^{N/2}`. The general setting imposes
no irreducibility assumption. It permits every family of even sizes tending
to infinity and uses a separate Gaussian coupling space at each size.
Real inverse temperature gives a positive real partition function; this
fact and the required integrability currently have proof placeholders.
:::

:::theorem "partition_function_clt" (parent := "central_limit_theorem") (uses := "clt_partition_function") (lean := "SYK.CLT.partition_clt, SYK.CLT.partition_and_log_partition_clt")
There are $`\beta_q>0` and a differentiable function $`\ell_q` on
$`(-\beta_q,\beta_q)` such that, for every such Majorana family and every
real $`|\beta|<\beta_q`,

$$`
\frac{1}{N}\log\mathbb E Z_N(\beta)\longrightarrow\ell_q(\beta),
\qquad
N^{q/2-1}(Y_N(\beta)-1)
\Longrightarrow\mathcal N(0,\rho_q^2(\beta)),
\qquad
\rho_q^2(\beta)=\frac{q!}{2}\beta^2(\ell_q'(\beta))^2.
`$$

For $`\beta\ne0`, the finite-model and limiting variances are positive and
$`(Z_N-\mathbb E Z_N)/\sqrt{\operatorname{Var}Z_N}` converges in
distribution to $`\mathcal N(0,1)`. At zero inverse temperature the relative
limit is the point mass at zero, and standardization is excluded.
The joint declaration gives the same radius and limiting function for the
logarithmic CLT. Its proof is a placeholder; the intended inputs are the
annealed limit, second-chaos identification, higher-chaos estimates, and
the classical central limit theorem.
:::

:::theorem "log_partition_clt" (parent := "central_limit_theorem") (uses := "partition_function_clt, log_partition_concentration") (lean := "SYK.CLT.log_partition_clt, SYK.CLT.partition_and_log_partition_clt")
With the same $`\beta_q`, $`\ell_q`, and variance as above, for every
real $`|\beta|<\beta_q`,

$$`
N^{q/2-1}\bigl(\log Z_N(\beta)-\mathbb E\log Z_N(\beta)\bigr)
\Longrightarrow\mathcal N(0,\rho_q^2(\beta)).
`$$

The centering is $`\mathbb E\log Z_N`, rather than
$`\log\mathbb E Z_N`. The intended argument uses the partition-function
CLT, local linearization of the logarithm, concentration, and control of
the negative tail and centering error. This proof remains a placeholder.
:::

:::theorem "free_energy_law_of_large_numbers" (parent := "central_limit_theorem") (uses := "log_partition_concentration")
The normalized logarithm of the partition function converges almost surely to
the limiting free-energy quantity on the parameter range stated in the
manuscript. The manuscript proof and its precise external inputs remain to be
completed and audited.
:::
