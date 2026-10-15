# Lean library

Start with [Main.lean](Main.lean) for the standalone Gaussian SYK model and public CLTs in `SYK.CLT.GaussianSYK`. The statement definitions use mathlib and this file alone; the joint proof uses the rest of the SYK library. [MainAudit.lean](MainAudit.lean) checks this statement boundary during the library build by following types and definition bodies while excluding theorem proofs.

For installation, see the [repository guide](../README.md#setup-instructions). For mathematical exposition and proof dependencies, read the [online Blueprint](https://TokyoProbabilityGroup.github.io/SYK_CLT/). Manuscript results are cited by their LaTeX labels in [the manuscript source](../Paper/).

## Central limit theorems

For fixed even $q \ge 4$, conditional on `hFE : AnnealedInput q S`, the theorems supply a common radius $\beta_q>0$ for real inverse temperatures $0<|\beta|<\beta_q$. The relative fluctuations $N^{q/2-1}(Z_N/\mathbb E Z_N-1)$ and centered logarithmic fluctuations $N^{q/2-1}(\log Z_N-\mathbb E\log Z_N)$ converge in distribution to centered Gaussians with variance $(q!/2)\beta^2(\ell_q'(\beta))^2$, where $\ell_q$ is the limit supplied by `hFE`. The standardized partition-function fluctuations converge to a centered Gaussian with variance $1$.

The public entry points are:

| Model | Import | Joint theorem |
| --- | --- | --- |
| Standalone Gaussian SYK | `SYK.Main` | `SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt` |
| Abstract family | `SYK.CLT.Main` | `SYK.CLT.partition_and_log_partition_clt` |
| Standard representation | `SYK.CLT.StandardModel` | `SYK.CLT.standard_partition_and_log_partition_clt` |

The [CLT chapter of the Blueprint](../Blueprint/SYKBlueprint/CLT.lean) explains the statements and normalizations.

## Annealed input

The CLTs are conditional on `hFE : AnnealedInput q S`. This structure records the conclusions of `prop:annealed-free-energy`: a limit $\ell_q$ that is even, convex, and $C^1$; locally uniform convergence of $N^{-1}\log\mathbb E Z_N$ and of its $\beta$-derivative to $\ell_q$ and $\ell_q'$; and $\beta\ell_q'(\beta)>0$ for $\beta\neq0$. The manuscript proves this proposition using results of He ([arXiv:2607.18998](https://arxiv.org/abs/2607.18998)) and a standard convergence theorem for convex functions. Neither these results nor this derivation are formalized, so the Lean theorems take the conclusions as an explicit hypothesis. The standalone `SYK.CLT.GaussianSYK.AnnealedInput` and the library's `SYK.CLT.AnnealedInput` have the same fields.

## Concentration of the log-partition function

`SYK.SuperConcentration.Main` proves that $\log Z$ is Lipschitz in the couplings (`SYK.logPartition_lipschitz`) and that its centered version satisfies a subgaussian MGF bound (`SYK.logPartition_hasSubgaussianMGF`) and a two-sided Gaussian tail bound (`SYK.logPartition_two_sided_tail_standardGaussian`). Here $Z=\operatorname{Tr}(\exp(-\beta H))$ uses the ordinary matrix trace, $H$ is built from any matrix Majorana system of positive finite dimension, and the couplings are independent standard Gaussians. The theorem statements give the exact constants. These results do not use the annealed input.

## Source guide

Paths below are relative to `SYK/`. Each module's opening docstring describes its role.

| Directory | Contents |
| --- | --- |
| [Model/](Model/) | Parameters, abstract Majorana systems, the standard representation, Gaussian disorder, and finite-dimensional Gibbs states |
| [Analysis/Matrix/](Analysis/Matrix/) | Singular values and trace-exponential bounds and derivatives |
| [Probability/GaussianChaos/](Probability/GaussianChaos/) | Gaussian Hermite expansion and integration by parts |
| [Probability/GaussianConcentration/](Probability/GaussianConcentration/) | Gaussian concentration, independent of the SYK model |
| [Probability/](Probability/) | Distribution transfer and moment results |
| [SuperConcentration/](SuperConcentration/) | Majorana bounds and concentration of the log-partition function |
| [CLT/](CLT/) | Finite models, chaos estimates, the quadratic CLT, limit transfer, logarithmic errors, and the CLT statements |

## Verification

To inspect the main results, open a scratch file at the repository root after `lake build`:

```lean
import SYK.Main
import SYK.CLT.StandardModel
import SYK.SuperConcentration.Main

#check SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt
#print axioms SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt
#check SYK.CLT.partition_and_log_partition_clt
#print axioms SYK.CLT.partition_and_log_partition_clt
#check SYK.CLT.standard_partition_and_log_partition_clt
#print axioms SYK.CLT.standard_partition_and_log_partition_clt
#print axioms SYK.logPartition_hasSubgaussianMGF
#print axioms SYK.logPartition_two_sided_tail_standardGaussian
```

Check the displayed assumptions, quantifier order, normalizations, and conclusions against the manuscript. For each theorem, `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. It does not show hypotheses: the CLTs still require `hFE`, as described in [Annealed input](#annealed-input).
