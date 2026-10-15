# Lean library

Start with [Main.lean](Main.lean) for the standalone Gaussian SYK model and public CLTs in `SYK.CLT.GaussianSYK`. The statement definitions use mathlib and this file alone; the joint proof uses the rest of the SYK library. [MainAudit.lean](MainAudit.lean) checks this statement boundary during the library build by following types and definition bodies while excluding theorem proofs.

For installation and the supported versions, see the [repository guide](../README.md#setup-instructions). For mathematical exposition and proof dependencies, read the [online Blueprint](https://TokyoProbabilityGroup.github.io/SYK_CLT/). The [manuscript](../Paper/CLT_SYK.tex) and its [sections](../Paper/sections/) record the paper's statements and arguments.

## Central limit theorems

For fixed even $q \ge 4$, conditional on `hFE : AnnealedInput q S`, the theorems supply a common radius $\beta_q>0$ for real inverse temperatures $0<|\beta|<\beta_q$. The relative fluctuations $N^{q/2-1}(Z_N/\mathbb E Z_N-1)$ and centered logarithmic fluctuations $N^{q/2-1}(\log Z_N-\mathbb E\log Z_N)$ converge in distribution to centered Gaussians with variance $(q!/2)\beta^2(\ell_q'(\beta))^2$. Here $\ell_q$ is the limit supplied by `hFE`; the standardized partition-function fluctuations converge to a centered Gaussian with variance $1$.

The abstract partition theorem and joint theorem in `SYK/CLT/Main.lean` are Lean-checked. `CLT/StandardModel.lean` applies them to the standard family `N=q+2*n`. The finite-model and Gaussian-chaos results, and the explicit logarithmic mean-error estimate, are also implemented. The annealed input is based on the manuscript's literature-based argument, described below.

The theorem statements are in `SYK/CLT/Main.lean` for an abstract family and in `CLT/StandardModel.lean` for the standard family; `AnnealedInput` is declared in `CLT/Basic.lean`. Under this input, `limitVariance_pos_of_ne_zero` gives positive limiting variance at every nonzero real inverse temperature; the high-temperature radius belongs to the CLT estimates. The CLT chapter of the [Blueprint](../Blueprint/SYKBlueprint/CLT.lean) explains the statements, normalization, and the boundary between formalized and assumed parts. Gaussian integration by parts and moment calculations are distinct from assuming the annealed limit.

The manuscript cites Y. He's *Free energy and spectral edge of the SYK model* (`He2026`, arXiv:2607.18998v3, Theorem 1.1 and Proposition 3.3) for the basic annealed limit in `thm: input`; see [the introduction](../Paper/sections/introduction.tex) and [bibliography](../Paper/CLT_SYK.tex). In [the proof of the main results](../Paper/sections/main-results.tex), `prop:annealed-free-energy` includes a proof using He's results, including Theorem 2.5, together with the normalization conversion and the convex-function convergence result `lem:convex-derivatives` (citing Rockafellar, Theorems 10.8 and 25.7). This establishes the regularity, locally uniform pressure and derivative limits, and strict sign needed here. The Lean structure [AnnealedInput](CLT/Basic.lean) takes the conclusions of that proposition as explicit hypotheses; the literature results and the manuscript's derivation of this input are outside the formalization scope.

The public entry points are:

| Model | Import | Joint theorem |
| --- | --- | --- |
| Standalone Gaussian SYK | `SYK.Main` | `SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt` |
| Abstract family | `SYK.CLT.Main` | `SYK.CLT.partition_and_log_partition_clt` |
| Standard representation | `SYK.CLT.StandardModel` | `SYK.CLT.standard_partition_and_log_partition_clt` |

## Gaussian concentration

The concentration modules provide Gaussian MGF and tail bounds for the log-partition function of the finite-dimensional Sachdev–Ye–Kitaev model. The proof combines a Majorana sum-of-squares estimate, the Gibbs-state derivative formula, and finite-dimensional Gaussian concentration. The public MGF includes zero inverse temperature; exponential tail formulas require positive inverse temperature and positive deviation.

With $Z=\operatorname{Tr}(\exp(-\beta H))$ using the ordinary matrix trace, probability and expectation are taken over independent standard Gaussian coordinates $g_A$ in the standard Hamiltonian. The centered $\log Z$ has subgaussian MGF parameter $\beta^2/q$ for every $\beta\ge0$. For $\beta>0$ and $t>0$,

$$
\mathbb P\!\left(|\log Z-\mathbb E[\log Z]|>t\right)
\le 2\exp\!\left(-\frac{q t^2}{2\beta^2}\right).
$$

The public entry point is `SYK.SuperConcentration.Main`. The exact assumptions, normalization, MGF parameter, and tail constants are those of its theorem statements, in particular `logPartition_lipschitz`, `logPartition_hasSubgaussianMGF`, and `logPartition_two_sided_tail_standardGaussian`. For these and the zero inverse-temperature statements, `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. These results are independent of the annealed input assumed by the CLTs.

Import `SYK.SuperConcentration.Main` to use these results.

## Source guide

Paths below are relative to `SYK/`. Each module's opening docstring describes its role and main declarations.

| Topic | Entry points |
| --- | --- |
| Model conventions and Majorana operators | [Model/Definitions.lean](Model/Definitions.lean), [Model/Majorana.lean](Model/Majorana.lean) |
| Standard representation and Gaussian disorder | [Model/StandardRepresentation.lean](Model/StandardRepresentation.lean), [Model/GaussianDisorder.lean](Model/GaussianDisorder.lean) |
| Gibbs states and matrix analysis | [Model/FiniteDimensionalGibbs.lean](Model/FiniteDimensionalGibbs.lean), [Analysis/Matrix/](Analysis/Matrix/) |
| Gaussian Hermite expansion and integration by parts | [Probability/GaussianChaos/](Probability/GaussianChaos/) |
| Gaussian concentration independent of the SYK model | [Probability/GaussianConcentration/](Probability/GaussianConcentration/) |
| Distribution transfer and independent moments | [Probability/](Probability/) |
| Finite partition functions and asymptotic assumptions | [CLT/FiniteModel.lean](CLT/FiniteModel.lean), [CLT/Basic.lean](CLT/Basic.lean) |
| Chaos estimates, quadratic CLT, limit transfer, and logarithmic errors | [CLT/Chaos/](CLT/Chaos/), [CLT/Quadratic/](CLT/Quadratic/), [CLT/Limit/](CLT/Limit/), [CLT/Log/](CLT/Log/) |
| Finite standard-representation normalization | [CLT/Normalization.lean](CLT/Normalization.lean) (`partitionFunction_standard`; not imported by the abstract CLT proofs) |
| Anticommuting-operator bounds and finite-size sum-of-squares estimates | [SuperConcentration/DensityMatrix.lean](SuperConcentration/DensityMatrix.lean), [SuperConcentration/MajoranaBound.lean](SuperConcentration/MajoranaBound.lean) |
| Log-partition Lipschitz, MGF, and tail bounds | [SuperConcentration/Main.lean](SuperConcentration/Main.lean) |

To locate a declaration and its callers, run `rg -n 'NAME' SYK` from the repository root.

## Verification

Build and file-checking commands are in the [repository guide](../README.md#building-and-testing).

For the main results, inspect their types and axiom dependencies in a Lean editor or scratch file at the repository root:

```lean
import SYK.Main
import SYK.CLT.StandardModel

#check SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt
#print axioms SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt
#check SYK.CLT.partition_and_log_partition_clt
#print axioms SYK.CLT.partition_and_log_partition_clt
#check SYK.CLT.standard_partition_and_log_partition_clt
#print axioms SYK.CLT.standard_partition_and_log_partition_clt
```

Check the displayed assumptions, quantifier order, normalizations, and conclusions against the manuscript. All these theorems require an explicit `hFE : AnnealedInput ...`; `#print axioms` checks their axiom dependencies but does not prove this input. These statement and assumption checks are needed when assessing which manuscript claims the formalization verifies, in addition to routine builds.

For the abstract CLTs and the standard-family joint theorem, the recorded axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`. Construction of the explicit annealed input is outside the Lean formalization scope, as described above.

When changing declarations referenced by the Blueprint, also follow the [documentation checks](../README.md#editing-and-checking). Manuscript compilation instructions are in the [repository guide](../README.md#manuscript).
