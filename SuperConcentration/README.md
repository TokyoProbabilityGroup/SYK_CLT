# Superconcentration of the SYK log-partition function

This directory formalizes a two-sided Gaussian concentration inequality for
the log-partition function of a finite-dimensional Sachdev–Ye–Kitaev (SYK)
model. The couplings are independent standard Gaussian random variables
indexed by the $q$-element subsets of $\{0,\ldots,N-1\}$.

## Main theorem

The public result is
`SYK.logPartition_two_sided_tail_standardGaussian` in `Main.lean`.
Let `P : SYK.Params`, let `M` be a finite-dimensional matrix realization of
the Majorana relations, and let $\mathcal J>0$, $\beta\ne0$, and $t>0$. Then

$$
\mathbb P\left(
  \left|\log Z-\mathbb E[\log Z]\right|>t
\right)
\le
2\exp\left(-\frac{q t^2}{2\beta^2\mathcal J^2}\right).
$$

Here $\beta=P.\beta$, and the probability and expectation are taken with
respect to the product standard Gaussian measure on the coupling space.

The normalized Hamiltonian uses

$$
\operatorname{couplingScale}(P,\mathcal J)
=
\mathcal J
\sqrt{\frac{(q-1)!}{N^{q-1}}}.
$$

The proof first obtains the exact finite-volume squared Lipschitz bound

$$
(\beta\,\operatorname{couplingScale}(P,\mathcal J))^2
\frac{\binom{N}{q-1}}{q},
$$

then bounds the Lipschitz constant by
$|\beta|\mathcal J/\sqrt q$. Applying finite-dimensional Gaussian
concentration gives the stated tail estimate. In particular, its scale is
independent of $N$.

The parameter structure `SYK.Params` assumes that $q$ is positive and even,
$q\le N$, and $\beta\ge0$. The public theorem additionally assumes
$\mathcal J>0$ and $\beta\ne0$. Empty matrix index types are handled inside
the theorem. The zero inverse-temperature case $\beta=0$, where the log-partition
function is constant, is covered separately by
`SYK.logPartition_tail_of_beta_zero`.

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

- `Core.lean` develops density-matrix identities, anticommuting-observable
  estimates, Majorana interaction algebra, and the model-specific
  sum-of-squares estimate.
- `Gibbs.lean` proves positivity and normalization properties of Gibbs states
  and differentiates traces of affine matrix exponentials.
- `GaussianConcentration/GaussianConcentrationAux.lean` supplies measure,
  integrability, gradient, and Herbst-method infrastructure.
- `GaussianConcentration/GaussianCovSmooth.lean` proves the smooth Gaussian
  covariance estimate using integration by parts and rotation invariance.
- `GaussianConcentration/GaussianCovMollify.lean` extends that estimate from
  smooth functions to Lipschitz functions by mollification.
- `GaussianConcentration/GaussianConcentration.lean` packages the
  moment-generating-function bounds and the one-sided and two-sided Gaussian
  tail inequalities.
- `Main.lean` defines the normalized Hamiltonian and log-partition
  function, proves the Lipschitz estimate, and states the public theorem.
- `blueprint_super_concentration.txt` and
  `GaussianConcentration/blueprint_gaussian_concentration.txt` contain proof
  plans. The Lean sources are authoritative if a blueprint records an older
  target.

## Building

The directory is built as the `SuperConcentration` Lean library in the shared
workspace. The project uses Lean 4.32.2 and Mathlib 4.32.2.

From the repository root, build the complete `SYK` library with:

```powershell
lake build SYK
```

To check only the public module, run:

```powershell
lake env lean SYK/SuperConcentration/Main.lean
```

Downstream Lean files can import the result with:

```lean
import SYK.SuperConcentration.Main
```
