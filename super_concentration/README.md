# Superconcentration of the SYK log-partition function

This directory formalizes a two-sided Gaussian concentration bound for the
log-partition function of a finite-dimensional Sachdev–Ye–Kitaev model. The
couplings are independent standard Gaussian variables indexed by the
$q$-element subsets of $\{0,\ldots,N-1\}$.

## Main result

The public theorem is
`SYK.logPartition_two_sided_tail_standardGaussian`, found in
`super_conc.lean`. For every valid parameter package `P`, matrix realization
`M` of the Majorana relations, and real coupling strength $J$, it constructs a
finite-volume constant $C$ such that, for every $t>0$,

$$
\mathbb P\left(
  \left|\log Z-\mathbb E[\log Z]\right|>t
\right)
\le
2\exp\left(-\frac{t^2}{2\varepsilon}\right),
$$

where

$$
\varepsilon
=
(\beta\,\operatorname{couplingScale}(P,J))^2
C N^{q/2}.
$$

The proof chooses

$$
C=
\frac{\binom{N}{q-1}/q}{N^{q/2}},
$$

using the exact finite-volume Majorana moment estimate proved in `core.lean`.
The theorem also handles an empty matrix index type and a zero concentration
scale directly.

The assumptions are bundled in `SYK.Params`: $q$ is positive and even,
$q\le N$, and the inverse temperature $\beta$ is nonnegative. No axiom,
`sorry`, or additional moment hypothesis occurs in this directory.

## File guide

- `core.lean` develops density-matrix identities, anticommuting-observable
  estimates, Majorana interaction algebra, and
  `syk_sum_sq_expectation_le`.
- `gibbs.lean` proves positivity and normalization properties of the Gibbs
  density matrix and differentiates traces of affine matrix exponentials.
- `Gaussian_concentration/GaussianConcentrationAux.lean` contains the measure,
  integrability, gradient, and Herbst-method infrastructure.
- `Gaussian_concentration/GaussianCovSmooth.lean` proves the smooth Gaussian
  covariance estimate by integration by parts and rotation invariance.
- `Gaussian_concentration/GaussianCovMollify.lean` transfers the covariance
  estimate from smooth functions to Lipschitz functions by mollification.
- `Gaussian_concentration/gaussian_concentration.lean` packages the
  moment-generating-function and one-sided and two-sided Gaussian tail bounds.
- `super_conc.lean` defines the normalized Hamiltonian and log-partition
  function, proves the required Lipschitz estimate, and states the public
  concentration theorem.
- `blueprint_super_concentration.txt` and
  `Gaussian_concentration/blueprint_gaussian_concentration.txt` record the
  proof plans. The Lean sources are authoritative where a blueprint describes
  an earlier target.

The dependency flow is

```text
Majorana moment bound
        |
Gibbs derivative formula
        |
Lipschitz bound for log Z
        |
finite-dimensional Gaussian concentration
        |
two-sided tail bound
```

## Building

This directory belongs to the `SYK` Lean library declared in the parent
workspace at `C:\Users\Public\Github\Lean`. That workspace currently uses
Lean 4.32.1 and Mathlib 4.32.1.

From `C:\Users\Public\Github\Lean`, build the complete library with

```powershell
lake build SYK
```

To check only the public module, run

```powershell
lake env lean SYK/super_concentration/super_conc.lean
```

Downstream Lean files can import the result with

```lean
import SYK.super_concentration.super_conc
```
