# Superconcentration of the SYK log-partition function

This directory formalizes Gaussian MGF and tail bounds for
the log-partition function of a finite-dimensional Sachdev–Ye–Kitaev (SYK)
model. The couplings are independent standard Gaussian random variables
indexed by the $q$-element subsets of $\{0,\ldots,N-1\}$.

## Main theorem

The public results in `Main.lean` are
`SYK.logPartition_hasSubgaussianMGF`,
`SYK.logPartition_upper_tail_standardGaussian`,
`SYK.logPartition_lower_tail_standardGaussian`, and
`SYK.logPartition_two_sided_tail_standardGaussian`.
Let `P : SYK.Params`, let `M` be a finite-dimensional matrix realization of
the Majorana relations, let `β : ℝ≥0`, and suppose that
$\beta\ne0$ and $t>0$. Then

$$
\mathbb P\left(
  \left|\log Z-\mathbb E[\log Z]\right|>t
\right)
\le
2\exp\left(-\frac{q t^2}{2\beta^2}\right).
$$

Each one-sided bound has the same exponential factor without the factor 2.
For every $\beta\ge0$, the centered log-partition function has
`HasSubgaussianMGF` parameter $\beta^2/q$: for every real $s$,
$\mathbb E\exp(s(\log Z-\mathbb E\log Z))\le\exp(s^2\beta^2/(2q))$.
These results prove the required Lipschitz estimate internally.

The inverse temperature is an explicit argument, and the probability and
expectation are taken with respect to the product standard Gaussian measure on
the coupling space.

The shared normalized Hamiltonian in `../Model/GaussianDisorder.lean` uses

$$
\operatorname{couplingScale}(P)
=
\sqrt{\frac{(q-1)!}{N^{q-1}}}.
$$

The proof first obtains the exact finite-volume squared Lipschitz bound

$$
(\beta\,\operatorname{couplingScale}(P))^2
\frac{\binom{N}{q-1}}{q},
$$

then bounds the Lipschitz constant by
$\beta/\sqrt q$. Applying finite-dimensional Gaussian
concentration gives the stated tail estimate. In particular, its scale is
independent of $N$.

The parameter structure `SYK.Params` assumes that $q$ is positive and even,
$q\le N$. The explicit inverse temperature has type `ℝ≥0`, and the public
tail theorems additionally assume $\beta\ne0$. The partition
function uses the ordinary matrix trace and satisfies $Z(0)=d$, where $d$ is
the matrix index dimension. The zero inverse-temperature case $\beta=0$,
where the log-partition function is the constant $\log d$, is covered separately by
`SYK.logPartition_tail_of_beta_zero`. The pointwise centered identity is
`SYK.logPartition_centered_of_beta_zero`; the MGF theorem includes this case.

All Lean source files in this directory are free of `axiom` declarations and
`sorry` placeholders.

## Proof outline

```text
Majorana sum-of-squares estimate
              |
Gibbs-state derivative formula
              |
Lipschitz bound for log Z
              |
Finite-dimensional Gaussian concentration
              |
Two-sided tail bound
```

The main model-specific input is the exact estimate
`SYK.syk_sum_sq_expectation_le`:

$$
\sum_{|I|=q}
\left\|\operatorname{Tr}(\rho\,\Psi_I)\right\|^2
\le
\frac{\binom{N}{q-1}}{q}
$$

for every density matrix $\rho$.

## File guide

- `DensityMatrix.lean` proves the expectation bound for anticommuting
  self-adjoint involutions, using the shared density-matrix API.
- `MajoranaBound.lean` proves the model-specific finite-size sum-of-squares
  estimate by extending interaction cores and double counting.
- `../Model/Majorana.lean` supplies the shared ordered interaction operators,
  word-reordering lemmas, and Majorana and interaction square identities.
- `../Model/FiniteDimensionalGibbs.lean` supplies density-matrix identities,
  positivity and normalization properties of Gibbs states, and derivatives of
  traces of affine matrix exponentials.
- `../Probability/GaussianConcentration/StandardGaussian.lean` supplies the
  standard measure, integrability, gradient, and Herbst-method infrastructure.
- `../Probability/GaussianConcentration/Smooth.lean` proves the smooth Gaussian
  covariance estimate using integration by parts and rotation invariance.
- `../Probability/GaussianConcentration/Lipschitz.lean` extends that estimate
  from smooth functions by mollification and packages the moment-generating
  function and tail bounds, including the zero-Lipschitz case.
- `../Model/GaussianDisorder.lean` defines the standard scale and Hamiltonian,
  their linearity, and self-adjointness. Its input is the standard Gaussian
  coordinate vector; each actual coefficient has variance $(q-1)!/N^{q-1}$.
- `Main.lean` defines the log-partition function using that shared Hamiltonian,
  proves the Lipschitz estimate, and supplies the MGF and tail theorems.
- `blueprint_super_concentration.txt` contains an older proof plan. The
  historical Gaussian-concentration plan remains under
  `GaussianConcentration/`; the Lean sources are authoritative.

## Building

The directory is built as the `SuperConcentration` Lean library in the shared
workspace. The project uses Lean 4.32.2 and Mathlib 4.32.2.

From the shared workspace root, build this library with:

```powershell
lake build SuperConcentration
```

To check only the public module, run:

```powershell
lake env lean SYK/SuperConcentration/Main.lean
```

Downstream Lean files can import the result with:

```lean
import SYK.SuperConcentration.Main
```
