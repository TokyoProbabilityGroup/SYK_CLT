module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import SYK.CLT.Main

import Mathlib.Analysis.Matrix.Normed -- shake: keep (Matrix.Norms.Operator scope)

public section

/-!
# Gaussian SYK: model, annealed assumptions, and two CLTs

All model definitions and assumptions are given in this file, using standard
Lean and mathlib notions. Both CLTs are conditional on `hFE : AnnealedInput q S`:
the convergence, differentiability, and sign assumptions on the limiting
annealed pressure are not established here, even for the concrete SYK model.

The joint theorem asserts the existence of one positive high-temperature
radius for both CLTs. The individual theorems are its projections.
Declarations from other SYK files are used only inside the joint proof,
after all model definitions, hypotheses, and CLT assertions.

The model corresponds to `subsec:SYK-model`, and the two claims to
`thm:partition-clt` and `thm:free-energy-clt`. Majorana matrices are abstract:
no particular representation is required. The assertions of
`prop:annealed-free-energy` are hypotheses collected in `AnnealedInput`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal Matrix.Norms.Operator

namespace SYK.CLT.GaussianSYK

noncomputable section

/-! ## Majorana operators and the family of systems -/

/-- Abstract Majorana matrices. `star` is the adjoint, and the matrix numeral
`2` means twice the identity. Thus the relations are
$\psi_i^*=\psi_i$ and $\psi_i\psi_j+\psi_j\psi_i=2\delta_{ij}I$;
in particular, different generators anticommute and $\psi_i^2=I$. -/
structure MajoranaOperators (N : ℕ) (d : Type) [Fintype d] [DecidableEq d] where
  /-- One matrix for each of the `N` generators. -/
  ψ : Fin N → Matrix d d ℂ
  /-- The matrices are self-adjoint. -/
  self_adjoint : ∀ i, star (ψ i) = ψ i
  /-- The canonical anticommutation relations. -/
  anticommutation : ∀ i j, ψ i * ψ j + ψ j * ψ i = if i = j then 2 else 0

/-- A fixed even interaction order `q ≥ 4` and a diverging sequence of even
sizes. `d n` indexes a nonempty finite matrix basis; its cardinality is the
representation dimension. For the full even-size limit take `N n = q + 2*n`.
No irreducibility or prescribed dimension is assumed. -/
structure Model (q : ℕ) where
  /-- Even interaction order. -/
  q_even : Even q
  /-- The interaction order is at least four. -/
  q_ge_four : 4 ≤ q
  /-- Number of generators in each system. -/
  N : ℕ → ℕ
  /-- Each system has even size. -/
  N_even : ∀ n, Even (N n)
  /-- Every size supports the interaction order. -/
  q_le_N : ∀ n, q ≤ N n
  /-- The sizes tend to infinity. -/
  N_tendsto : Tendsto N atTop atTop
  /-- Matrix basis index type at each size. -/
  d : ℕ → Type
  /-- Finite-dimensional representations. -/
  fintype : ∀ n, Fintype (d n)
  /-- Decidable equality for matrix operations. -/
  decidableEq : ∀ n, DecidableEq (d n)
  /-- Positive representation dimensions. -/
  nonempty : ∀ n, Nonempty (d n)
  /-- Majorana matrices satisfying the displayed relations. -/
  majorana : ∀ n,
    letI := fintype n
    letI := decidableEq n
    MajoranaOperators (N n) (d n)

attribute [instance] Model.fintype Model.decidableEq Model.nonempty

/-! ## Gaussian disorder and Hamiltonian -/

/-- An interaction is a `q`-element subset of the generator labels. -/
abbrev InteractionLabels (N q : ℕ) := {I : Finset (Fin N) // I.card = q}

/-- One real coordinate `g I` for each interaction, with Euclidean norm. -/
abbrev Couplings (N q : ℕ) := EuclideanSpace ℝ (InteractionLabels N q)

/-- Independent standard normal coordinates. `gaussianReal m v` is the
normal law with mean `m` and variance `v : ℝ≥0`. `Measure.pi` forms the
product law; `WithLp.toLp 2` identifies the coordinates with their Euclidean
vector, without changing them. -/
def disorderLaw (N q : ℕ) : Measure (Couplings N q) :=
  (Measure.pi fun _ : InteractionLabels N q ↦ gaussianReal 0 1).map (WithLp.toLp 2)

instance (N q : ℕ) : IsProbabilityMeasure (disorderLaw N q) := by
  unfold disorderLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

variable {q : ℕ} (S : Model q)

/-- $\sigma_N=\sqrt{(q-1)!/N^{q-1}}$: the physical coupling
$J_I=\sigma_N g_I$ has variance $(q-1)!/N^{q-1}$. -/
def Model.couplingScale (n : ℕ) : ℝ :=
  Real.sqrt ((q - 1).factorial / (S.N n : ℝ) ^ (q - 1))

/-- $\Psi_I=\mathrm i^{q/2}\psi_{i_1}\cdots\psi_{i_q}$, with
$i_1<\cdots<i_q$. Sorting fixes the order of the matrix product. -/
def Model.interactionOperator (n : ℕ) (I : InteractionLabels (S.N n) q) :
    Matrix (S.d n) (S.d n) ℂ :=
  Complex.I ^ (q / 2) • ((I.1.sort (· ≤ ·)).map (S.majorana n).ψ).prod

/-- The Gaussian SYK Hamiltonian $H_N(g)=\sum_{|I|=q}\sigma_N g_I\Psi_I$.
Here `•` denotes scalar multiplication of matrices. -/
def Model.H (n : ℕ) (g : Couplings (S.N n) q) : Matrix (S.d n) (S.d n) ℂ :=
  ∑ I : InteractionLabels (S.N n) q,
    ((S.couplingScale n * g I : ℝ) : ℂ) • S.interactionOperator n I

/-! ## Partition function, expectations, and variance -/

/-- $Z_N(\beta;g)=d_N^{-1}\operatorname{Tr}\exp(-\beta H_N(g))$,
where $d_N$ is the actual matrix dimension. The trace is real at real
inverse temperature; `.re` takes its real part. In the standard
representation $d_N=2^{N/2}$. -/
def Model.Z (β : ℝ) (n : ℕ) (g : Couplings (S.N n) q) : ℝ :=
  (Matrix.trace (NormedSpace.exp (-(β : ℂ) • S.H n g)) /
    (Fintype.card (S.d n) : ℂ)).re

/-- Disorder expectation $\mathbb E Z_N(\beta)$. -/
def Model.meanZ (β : ℝ) (n : ℕ) : ℝ :=
  ∫ g, S.Z β n g ∂disorderLaw (S.N n) q

/-- Disorder expectation $\mathbb E\log Z_N(\beta)$. -/
def Model.meanLogZ (β : ℝ) (n : ℕ) : ℝ :=
  ∫ g, Real.log (S.Z β n g) ∂disorderLaw (S.N n) q

/-- Disorder variance $\mathbb E[(Z_N-\mathbb E Z_N)^2]$. -/
def Model.varianceZ (β : ℝ) (n : ℕ) : ℝ :=
  ∫ g, (S.Z β n g - S.meanZ β n) ^ 2 ∂disorderLaw (S.N n) q

/-! ## Annealed input

The following are assumptions on the partition functions just defined.
`ConvexOn ℝ Set.univ` means convexity on the whole real line,
`ContDiff ℝ 1` means $C^1$, and `deriv ℓ β` is $\ell'(\beta)$.
The two limits are locally uniform on $\mathbb R$, that is, uniform on
each compact subset as `n → ∞`. Packaging these assumptions does not
prove the annealed proposition or construct its limiting function.
-/

/-- The assertions of `prop:annealed-free-energy` for this model family. -/
structure AnnealedInput (q : ℕ) (S : Model q) where
  /-- Limiting annealed pressure. -/
  ℓ : ℝ → ℝ
  /-- Evenness. -/
  even : ∀ β : ℝ, ℓ (-β) = ℓ β
  /-- Convexity on the whole real line. -/
  convex : ConvexOn ℝ Set.univ ℓ
  /-- Continuous differentiability. -/
  contDiff_one : ContDiff ℝ 1 ℓ
  /-- Locally uniform convergence of the annealed pressure. -/
  pressure_limit : TendstoLocallyUniformlyOn
    (fun n β ↦ Real.log (S.meanZ β n) / (S.N n : ℝ)) ℓ atTop Set.univ
  /-- Locally uniform convergence of its temperature derivative. -/
  derivative_limit : TendstoLocallyUniformlyOn
    (fun n β ↦ deriv (fun b ↦ Real.log (S.meanZ b n)) β / (S.N n : ℝ))
    (deriv ℓ) atTop Set.univ
  /-- Nondegeneracy at every nonzero real inverse temperature. -/
  sign : ∀ β : ℝ, β ≠ 0 → 0 < β * deriv ℓ β

/-- Common limiting variance $\rho_q^2(\beta)=\frac{q!}{2}\beta^2(\ell'(\beta))^2$.
The proof of nonnegativity uses only the displayed formula. -/
def limitVariance (ℓ : ℝ → ℝ) (β : ℝ) : ℝ≥0 :=
  ⟨(q.factorial : ℝ) / 2 * β ^ 2 * (deriv ℓ β) ^ 2, by positivity⟩

/-! ## The two CLT assertions

`TendstoInDistribution X atTop (fun x : ℝ ↦ x) μ (gaussianReal 0 v)`
means $X_n\Rightarrow\mathcal N(0,v)$: the variables are almost everywhere
measurable and, for every bounded continuous $f:\mathbb R\to\mathbb R$,
$\int f(X_n(g))\,d\mu_n(g)\to\int f(x)\,d\mathcal N(0,v)(x)$.
Different sizes may have different probability spaces. Powers in the
scaling have natural exponents; evenness makes `q / 2 - 1` exactly $q/2-1$.
-/

/-- The relative and standardized partition-function CLTs, together with
positivity of the limiting variance and all finite variances. -/
def PartitionCLTAt (ℓ : ℝ → ℝ) (β : ℝ) : Prop :=
  TendstoInDistribution
    (fun n (g : Couplings (S.N n) q) ↦
      (S.N n : ℝ) ^ (q / 2 - 1) * (S.Z β n g / S.meanZ β n - 1))
    atTop (fun x : ℝ ↦ x) (fun n ↦ disorderLaw (S.N n) q)
    (gaussianReal 0 (limitVariance (q := q) ℓ β)) ∧
  0 < limitVariance (q := q) ℓ β ∧ (∀ n, 0 < S.varianceZ β n) ∧
  TendstoInDistribution
    (fun n (g : Couplings (S.N n) q) ↦
      (S.Z β n g - S.meanZ β n) / Real.sqrt (S.varianceZ β n))
    atTop (fun x : ℝ ↦ x) (fun n ↦ disorderLaw (S.N n) q) (gaussianReal 0 1)

/-- The log-partition CLT, centered by the expectation of the logarithm. -/
def LogPartitionCLTAt (ℓ : ℝ → ℝ) (β : ℝ) : Prop :=
  TendstoInDistribution
    (fun n (g : Couplings (S.N n) q) ↦
      (S.N n : ℝ) ^ (q / 2 - 1) * (Real.log (S.Z β n g) - S.meanLogZ β n))
    atTop (fun x : ℝ ↦ x) (fun n ↦ disorderLaw (S.N n) q)
    (gaussianReal 0 (limitVariance (q := q) ℓ β))

/-! ## Conditional CLT theorems

The model and `AnnealedInput` imply the existence of a common positive radius
$\beta_q$ on which both CLTs hold. No radius is defined by selecting from the
desired conclusions. The range $0<|\beta|<\beta_q$ is written as
`|β| < βq` and `β ≠ 0` in the statements below.
-/

/-- `thm:partition-clt` and `thm:free-energy-clt`, conditional on the
assertions of `prop:annealed-free-energy` supplied by `hFE`.
There exists one positive radius such that, for every $0<|\beta|<\beta_q$,
the relative, standardized, and centered log-partition CLTs hold with the
displayed limiting variance. The limiting and finite variances are positive. -/
theorem syk_partition_and_log_partition_clt (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq → β ≠ 0 →
        PartitionCLTAt S hFE.ℓ β ∧ LogPartitionCLTAt S hFE.ℓ β := by
  let T : SYK.CLT.Setting q := {
    q_even := S.q_even, q_ge_four := S.q_ge_four, N := S.N,
    N_even := S.N_even, q_le_N := S.q_le_N, N_tendsto := S.N_tendsto,
    d := S.d, fintype := S.fintype, decidableEq := S.decidableEq,
    nonempty := S.nonempty,
    majorana := fun n ↦ {
      ψ := (S.majorana n).ψ,
      majorana_rel := (S.majorana n).anticommutation,
      self_adjoint := (S.majorana n).self_adjoint } }
  -- The disorder law, Hamiltonian, partition function, and means agree definitionally.
  let hT : SYK.CLT.AnnealedInput q T := {
    ℓ := hFE.ℓ, even := hFE.even, convex := hFE.convex,
    contDiff_one := hFE.contDiff_one, pressure_limit := hFE.pressure_limit,
    derivative_limit := hFE.derivative_limit, sign := hFE.sign }
  -- The imported variance equals the locally defined centered second-moment integral.
  have hvar (β : ℝ) (n : ℕ) : T.varianceZ β n = S.varianceZ β n :=
    variance_eq_integral (T.partition_moments β n).1.aemeasurable
  obtain ⟨βq, hβq, h⟩ := SYK.CLT.partition_and_log_partition_clt T hT
  refine ⟨βq, hβq, fun β hβ hβ0 ↦ ?_⟩
  have hb := h β hβ hβ0
  dsimp only [PartitionCLTAt, LogPartitionCLTAt]
  simp_rw [← hvar]
  exact ⟨⟨hb.2.1, hb.2.2.2⟩, hb.2.2.1⟩

/-- `thm:partition-clt`: conditional on `hFE`, there is a positive radius
such that both partition-function CLTs hold for every $0<|\beta|<\beta_q$.
The joint theorem also supplies the log-partition CLT at this radius. -/
theorem syk_partition_clt (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq → β ≠ 0 → PartitionCLTAt S hFE.ℓ β := by
  obtain ⟨βq, hβq, h⟩ := syk_partition_and_log_partition_clt S hFE
  exact ⟨βq, hβq, fun β hβ hβ0 ↦ (h β hβ hβ0).1⟩

/-- `thm:free-energy-clt`: conditional on `hFE`, there is a positive radius with
$N^{q/2-1}(\log Z_N-\mathbb E\log Z_N)\Rightarrow\mathcal N(0,\rho_q^2(\beta))$.
The joint theorem supplies a common radius for this and the partition CLTs.
Both main results exclude `β = 0`. -/
theorem syk_log_partition_clt (hFE : AnnealedInput q S) :
    ∃ βq : ℝ, 0 < βq ∧
      ∀ β : ℝ, |β| < βq → β ≠ 0 → LogPartitionCLTAt S hFE.ℓ β := by
  obtain ⟨βq, hβq, h⟩ := syk_partition_and_log_partition_clt S hFE
  exact ⟨βq, hβq, fun β hβ hβ0 ↦ (h β hβ hβ0).2⟩

end

end SYK.CLT.GaussianSYK
