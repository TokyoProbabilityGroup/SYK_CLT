# Superconcentration of the SYK log-partition function

This directory provides Gaussian MGF and tail bounds for the log-partition function of the finite-dimensional Sachdev–Ye–Kitaev model. The proof combines a Majorana sum-of-squares estimate, the Gibbs-state derivative formula, and finite-dimensional Gaussian concentration. The public MGF includes zero inverse temperature; exponential tail formulas require positive inverse temperature and positive deviation.

With $Z=\operatorname{Tr}(\exp(-\beta H))$ using the ordinary matrix trace, probability and expectation are taken over independent standard Gaussian coordinates $g_A$ in the standard Hamiltonian. The centered $\log Z$ has subgaussian MGF parameter $\beta^2/q$ for every $\beta\ge0$. For $\beta>0$ and $t>0$,

$$
\mathbb P\!\left(|\log Z-\mathbb E[\log Z]|>t\right)
\le 2\exp\!\left(-\frac{q t^2}{2\beta^2}\right).
$$

The public entry point is `SYK.SuperConcentration.Main`. The exact assumptions, normalization, MGF parameter, and tail constants are those of its theorem statements, in particular `logPartition_lipschitz`, `logPartition_hasSubgaussianMGF`, and `logPartition_two_sided_tail_standardGaussian`. For these and the zero-temperature statements, `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. These results are independent of the annealed input assumed by the CLTs.

## File guide

| File | Role |
| --- | --- |
| `DensityMatrix.lean` | Expectation bounds for anticommuting self-adjoint involutions |
| `MajoranaBound.lean` | Finite-size sum-of-squares bound by extension and double counting |
| `Main.lean` | Log-partition function, Lipschitz estimate, MGF, and tail bounds |
| `../Model/Majorana.lean` | Ordered interaction operators and shared algebraic identities |
| `../Model/FiniteDimensionalGibbs.lean` | Density matrices, Gibbs states, and trace-exponential derivatives |
| `../Model/GaussianDisorder.lean` | Standard Gaussian coupling space, scale, and Hamiltonian |
| `../Probability/GaussianConcentration/` | Standard measure, smooth covariance estimates, mollification, and concentration |

## Building

From the repository root (`SYK_CLT/`):

```bash
lake build SYK
lake lean SYK/SuperConcentration/Main.lean
```

Downstream Lean files can import the result with:

```lean
import SYK.SuperConcentration.Main
```

See [the repository guide](../../README.md#building-and-testing) for the supported environment, full build, and separate theorem-statement and axiom checks. Build success does not establish agreement with every informal mathematical claim.
