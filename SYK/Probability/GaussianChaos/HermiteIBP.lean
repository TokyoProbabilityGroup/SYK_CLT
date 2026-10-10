import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import SYK.Probability.GaussianConcentration.StandardGaussian
import SYK.Probability.GaussianChaos.Basic

/-!
# Iterated Gaussian integration by parts

The theorem `hermiteMulti_ibp_of_expGrowth` proves the general identity in
`lem:Gaussian-Hermite-IBP` of `Paper/sections/gaussian-chaos.tex`, with
exactly its `C^{|α|}` regularity and exponential Euclidean-growth assumptions
for the partial derivatives `η ≤ α`. Iterating the creation operator
`g_i - ∂_i` along `multiIndexList α` gives the product `hermiteMulti α` of
probabilists' Hermite polynomials (`hermiteList_multiIndexList`). Derivative
order independence, the intermediate product bounds, and integrability are
proved here; `ExpIBPChain` is only an internal sufficient condition for iteration.
Applying the lemma to a concrete function such as `Z_N` is left to the users of this module.
-/

open MeasureTheory ProbabilityTheory

namespace SYK.GaussianChaos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative along coordinate `i`, defined using a one-dimensional slice. -/
noncomputable def coordDeriv (i : ι) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun g => deriv (fun x => f (Function.update g i x)) (g i)

/-- Identify the slice derivative with the Fréchet derivative in the selected
coordinate when the function is continuously differentiable. -/
theorem coordDeriv_eq_fderiv (i : ι)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (g : ι → ℝ) :
    coordDeriv i f g = (fderiv ℝ f g) (Pi.single i 1) := by
  have hupdate : HasDerivAt (fun x => Function.update g i x) (Pi.single i 1) (g i) :=
    hasDerivAt_update g i (g i)
  have h := (hf.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    (g i) hupdate
  simpa [coordDeriv, Function.comp_def] using h.deriv

/-- Exponential-growth Stein identity on a finite product Gaussian. Only the
chosen coordinate derivative needs a growth bound. -/
theorem coord_stein_of_expGrowth
    (h : (ι → ℝ) → ℝ) (i : ι) (hh : ContDiff ℝ 1 h)
    (C c : ℝ)
    (hhb : ∀ g, |h g| ≤ C * Real.exp (c * ∑ j, |g j|))
    (hdb : ∀ g, |coordDeriv i h g| ≤ C * Real.exp (c * ∑ j, |g j|)) :
    (∫ g, g i * h g ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, coordDeriv i h g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hdb' : ∀ g, |(fderiv ℝ h g) (Pi.single i 1)| ≤
      C * Real.exp (c * ∑ j, |g j|) := by
    intro g
    simpa [coordDeriv_eq_fderiv i hh g] using hdb g
  simpa only [← coordDeriv_eq_fderiv i hh] using
    SYK.GaussianConcentration.pi_gaussian_stein_coord h i hh C c hhb hdb'

omit [DecidableEq ι] in
/-- The bound for the Euclidean norm used for the disorder vector
in the manuscript. -/
theorem euclidean_norm_le_sum_abs (g : ι → ℝ) :
    ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖ ≤ ∑ j, |g j| := by
  classical
  have hsum : (WithLp.toLp 2 g : EuclideanSpace ℝ ι) =
      ∑ j, EuclideanSpace.single j (g j) := by
    ext i
    simp
  calc
    ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖ =
        ‖∑ j, EuclideanSpace.single j (g j)‖ := congrArg norm hsum
    _ ≤ ∑ j, ‖EuclideanSpace.single j (g j)‖ := norm_sum_le _ _
    _ = ∑ j, |g j| := by simp

/-- Every nonnegative real power is bounded by an exponential with linear argument. -/
private theorem pow_le_exp_nat_mul (x : ℝ) (n : ℕ) (hx : 0 ≤ x) :
    x ^ n ≤ Real.exp ((n : ℝ) * x) := by
  have h : x ≤ Real.exp x := by
    nlinarith [Real.add_one_le_exp x]
  calc
    x ^ n ≤ (Real.exp x) ^ n := pow_le_pow_left₀ hx h n
    _ = Real.exp ((n : ℝ) * x) := by rw [← Real.exp_nat_mul]

/-- Evaluation of a fixed integer polynomial grows at most exponentially. -/
private theorem polynomial_aeval_exp_bound (p : Polynomial ℤ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧
      ∀ x : ℝ, |Polynomial.aeval x p| ≤ C * Real.exp (c * |x|) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨Cp, cp, hCp, hcp, hp⟩ := hp
      obtain ⟨Cq, cq, hCq, hcq, hq⟩ := hq
      refine ⟨Cp + Cq, max cp cq, by positivity, by positivity, ?_⟩
      intro x
      rw [map_add]
      have hpe : Real.exp (cp * |x|) ≤ Real.exp (max cp cq * |x|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      have hqe : Real.exp (cq * |x|) ≤ Real.exp (max cp cq * |x|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
      have hp' := (hp x).trans (mul_le_mul_of_nonneg_left hpe hCp)
      have hq' := (hq x).trans (mul_le_mul_of_nonneg_left hqe hCq)
      nlinarith [abs_add_le (Polynomial.aeval x p) (Polynomial.aeval x q)]
  | monomial n a =>
      refine ⟨|a|, n, abs_nonneg _, by positivity, ?_⟩
      intro x
      simp only [Polynomial.aeval_monomial, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_exp_nat_mul |x| n (abs_nonneg _)) (abs_nonneg _)

omit [DecidableEq ι] in
/-- A single coordinate is bounded by the Euclidean norm. -/
private theorem abs_coord_le_euclidean_norm (g : ι → ℝ) (i : ι) :
    |g i| ≤ ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖ := by
  simpa only [Real.norm_eq_abs] using
    (PiLp.norm_apply_le (WithLp.toLp 2 g : EuclideanSpace ℝ ι) i)

omit [DecidableEq ι] in
/-- A fixed Hermite factor has exponential growth in the disorder norm. -/
theorem hermite_factor_exp_bound (i : ι) (n : ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ g : ι → ℝ,
      |Polynomial.aeval (g i) (Polynomial.hermite n)| ≤
        C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
  obtain ⟨C, c, hC, hc, hp⟩ := polynomial_aeval_exp_bound (Polynomial.hermite n)
  refine ⟨C, c, hC, hc, ?_⟩
  intro g
  exact (hp (g i)).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (abs_coord_le_euclidean_norm g i) hc)) hC)

omit [DecidableEq ι] in
/-- A finite product of Hermite factors has exponential Euclidean growth. -/
theorem hermite_product_exp_bound (α : ι → ℕ) (s : Finset ι) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ g : ι → ℝ,
      |∏ i ∈ s, Polynomial.aeval (g i) (Polynomial.hermite (α i))| ≤
        C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine ⟨1, 0, by positivity, le_rfl, ?_⟩
      intro g
      simp
  | @insert i s his ih =>
      obtain ⟨Ci, ci, hCi, hci, hi⟩ := hermite_factor_exp_bound i (α i)
      obtain ⟨Cs, cs, hCs, hcs, hs⟩ := ih
      refine ⟨Ci * Cs, ci + cs, by positivity, by positivity, ?_⟩
      intro g
      simp only [Finset.prod_insert his]
      rw [abs_mul]
      have hprod := mul_le_mul (hi g) (hs g) (abs_nonneg _) (by positivity)
      calc
        |Polynomial.aeval (g i) (Polynomial.hermite (α i))| *
            |∏ j ∈ s, Polynomial.aeval (g j) (Polynomial.hermite (α j))| ≤
          (Ci * Real.exp (ci * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) *
            (Cs * Real.exp (cs * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) := hprod
        _ = (Ci * Cs) * Real.exp ((ci + cs) *
            ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
          rw [add_mul, Real.exp_add]
          ring

/-- Selected-coordinate Stein identity using the Euclidean norm from the
manuscript's exponential-growth condition. -/
theorem coord_stein_of_euclidean_expGrowth
    (h : (ι → ℝ) → ℝ) (i : ι) (hh : ContDiff ℝ 1 h)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hhb : ∀ g, |h g| ≤ C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (hdb : ∀ g, |coordDeriv i h g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    (∫ g, g i * h g ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, coordDeriv i h g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hbound (g : ι → ℝ) :
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) ≤
        C * Real.exp (c * ∑ j, |g j|) := by
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (euclidean_norm_le_sum_abs g) hc)
  exact coord_stein_of_expGrowth h i hh C c
    (fun g => (hhb g).trans (hbound g))
    (fun g => (hdb g).trans (hbound g))

/-- Iterate coordinate derivatives in the order given by a list. -/
noncomputable def partialList :
    List ι → ((ι → ℝ) → ℝ) → (ι → ℝ) → ℝ
  | [], f => f
  | i :: l, f => partialList l (coordDeriv i f)

omit [Fintype ι] in
/-- Splitting an ordered list of partial derivatives at any prefix. -/
theorem partialList_append (l₁ l₂ : List ι) (f : (ι → ℝ) → ℝ) :
    partialList (l₁ ++ l₂) f = partialList l₂ (partialList l₁ f) := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons i l ih =>
      simpa [partialList] using ih (coordDeriv i f)

/-- The coordinate creation operator $g_i-\partial_i$. -/
noncomputable def creation (i : ι) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun g => g i * f g - coordDeriv i f g

/-- Product rule for the selected coordinate derivative. -/
theorem coordDeriv_mul (i : ι) {f h : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h) (g : ι → ℝ) :
    coordDeriv i (fun x => f x * h x) g =
      coordDeriv i f g * h g + f g * coordDeriv i h g := by
  rw [coordDeriv_eq_fderiv i (hf.mul hh),
    coordDeriv_eq_fderiv i hf, coordDeriv_eq_fderiv i hh,
    fderiv_fun_mul (hf.differentiable (by norm_num) g)
      (hh.differentiable (by norm_num) g)]
  simp [smul_eq_mul]
  ring

/-- Continuity of a coordinate derivative of a continuously differentiable
function. -/
theorem continuous_coordDeriv (i : ι) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) : Continuous (coordDeriv i f) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have h : Continuous (fun g => (fderiv ℝ f g) (Pi.single i 1)) :=
    hfd.clm_apply continuous_const
  simpa only [← coordDeriv_eq_fderiv i hf] using h

/-- Coordinate differentiation preserves smoothness of every finite order. -/
theorem contDiff_coordDeriv (i : ι) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ ⊤ f) : ContDiff ℝ ⊤ (coordDeriv i f) := by
  have hfd : ContDiff ℝ ⊤ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hconst : ContDiff ℝ ⊤
      (fun _ : ι → ℝ => (Pi.single i (1 : ℝ) : ι → ℝ)) := by
    fun_prop
  have h := hfd.clm_apply hconst
  simpa only [← coordDeriv_eq_fderiv i (hf.of_le (by norm_num))] using h

/-- One coordinate derivative reduces a finite differentiability order by
one. -/
theorem contDiff_coordDeriv_succ (i : ι) (n : ℕ)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (coordDeriv i f) := by
  have hfd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hconst : ContDiff ℝ n
      (fun _ : ι → ℝ => (Pi.single i (1 : ℝ) : ι → ℝ)) := by
    fun_prop
  have h := hfd.clm_apply hconst
  simpa only [← coordDeriv_eq_fderiv i (hf.of_le (by norm_num))] using h

/-- Iterating a prescribed list of coordinate derivatives consumes exactly
the length of that list from the differentiability order. -/
theorem contDiff_partialList (l : List ι) (n : ℕ)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (l.length + n) f) :
    ContDiff ℝ n (partialList l f) := by
  induction l generalizing f with
  | nil => simpa [partialList] using hf
  | cons i l ih =>
      have hf' : ContDiff ℝ (l.length + n + 1) f := by
        convert hf using 1
        simp [List.length_cons, add_assoc, add_comm]
      have hd : ContDiff ℝ (l.length + n) (coordDeriv i f) :=
        contDiff_coordDeriv_succ i (l.length + n) hf'
      simpa [partialList] using ih hd

omit [DecidableEq ι] in
/-- A continuous function with an exponential Euclidean-norm bound is
integrable against the finite product standard Gaussian. -/
theorem integrable_of_euclidean_expBound
    (h : (ι → ℝ) → ℝ) (hh : Continuous h)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hb : ∀ g, |h g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    Integrable h (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hbase : Integrable (fun g : ι → ℝ => C * Real.exp (c * ∑ j, |g j|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    (SYK.GaussianConcentration.integrable_exp_c_sum_abs_pi c).const_mul C
  apply hbase.mono' hh.aestronglyMeasurable
  filter_upwards [] with g
  rw [Real.norm_eq_abs]
  exact (hb g).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (euclidean_norm_le_sum_abs g) hc)) hC)

omit [DecidableEq ι] in
/-- The same bound remains integrable after multiplication by one Gaussian
coordinate. -/
theorem integrable_coord_mul_of_euclidean_expBound
    (h : (ι → ℝ) → ℝ) (hh : Continuous h) (i : ι)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hb : ∀ g, |h g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    Integrable (fun g => g i * h g)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hbase : Integrable
      (fun g : ι → ℝ => C * (|g i| * Real.exp (c * ∑ j, |g j|)))
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    (SYK.GaussianConcentration.integrable_abs_coord_mul_exp_c_sum_abs_pi c i).const_mul C
  apply hbase.mono' ((continuous_apply i).mul hh).aestronglyMeasurable
  filter_upwards [] with g
  change |g i * h g| ≤ C * (|g i| * Real.exp (c * ∑ j, |g j|))
  rw [abs_mul]
  have hbound : |h g| ≤ C * Real.exp (c * ∑ j, |g j|) :=
    (hb g).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (euclidean_norm_le_sum_abs g) hc)) hC)
  calc
    |g i| * |h g| ≤ |g i| * (C * Real.exp (c * ∑ j, |g j|)) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = C * (|g i| * Real.exp (c * ∑ j, |g j|)) := by ring

/-- A creation-operator IBP step obtained from the selected-coordinate
exponential-growth Stein identity. The integrability hypotheses isolate the
linear integral rearrangement; they will follow from growth bounds in the
multi-index application. -/
theorem creation_ibp_of_expGrowth
    (i : ι) (φ ψ : (ι → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hhb : ∀ g, |φ g * ψ g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (hdb : ∀ g, |coordDeriv i (fun x => φ x * ψ x) g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (hA : Integrable (fun g => g i * (φ g * ψ g))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hB : Integrable (fun g => coordDeriv i φ g * ψ g)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hD : Integrable (fun g => φ g * coordDeriv i ψ g)
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    (∫ g, creation i φ g * ψ g ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, φ g * coordDeriv i ψ g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  let A : (ι → ℝ) → ℝ := fun g => g i * (φ g * ψ g)
  let B : (ι → ℝ) → ℝ := fun g => coordDeriv i φ g * ψ g
  let D : (ι → ℝ) → ℝ := fun g => φ g * coordDeriv i ψ g
  have hstein : (∫ g, A g ∂γ) = ∫ g, B g + D g ∂γ := by
    simpa only [γ, A, B, D, coordDeriv_mul i hφ hψ] using
      coord_stein_of_euclidean_expGrowth
        (fun g => φ g * ψ g) i (hφ.mul hψ) C c hc hC hhb hdb
  calc
    (∫ g, creation i φ g * ψ g ∂γ) = ∫ g, A g - B g ∂γ := by
      congr 1
      funext g
      simp [A, B, creation]
      ring
    _ = (∫ g, A g ∂γ) - ∫ g, B g ∂γ := integral_sub hA hB
    _ = (∫ g, B g + D g ∂γ) - ∫ g, B g ∂γ := by rw [hstein]
    _ = ∫ g, D g ∂γ := by rw [integral_add hB hD]; ring

/-- A creation-operator step from exponential bounds for exactly the three
products that occur in the product rule. No integrability assumptions remain. -/
theorem creation_ibp_of_expProductBounds
    (i : ι) (φ ψ : (ι → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ)
    (C c : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (h0 : ∀ g, |φ g * ψ g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (h1 : ∀ g, |coordDeriv i φ g * ψ g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖))
    (h2 : ∀ g, |φ g * coordDeriv i ψ g| ≤
      C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    (∫ g, creation i φ g * ψ g ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, φ g * coordDeriv i ψ g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h0' : ∀ g, |φ g * ψ g| ≤
      (2 * C) * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
    intro g
    have he : 0 ≤ Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) :=
      Real.exp_nonneg _
    nlinarith [h0 g]
  have hd' : ∀ g, |coordDeriv i (fun x => φ x * ψ x) g| ≤
      (2 * C) * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
    intro g
    rw [coordDeriv_mul i hφ hψ g]
    exact (abs_add_le _ _).trans (by nlinarith [h1 g, h2 g])
  have hA : Integrable (fun g => g i * (φ g * ψ g))
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    integrable_coord_mul_of_euclidean_expBound
      (fun g => φ g * ψ g) (hφ.continuous.mul hψ.continuous) i C c hc hC h0
  have hB : Integrable (fun g => coordDeriv i φ g * ψ g)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    integrable_of_euclidean_expBound _
      ((continuous_coordDeriv i hφ).mul hψ.continuous) C c hc hC h1
  have hD : Integrable (fun g => φ g * coordDeriv i ψ g)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    integrable_of_euclidean_expBound _
      (hφ.continuous.mul (continuous_coordDeriv i hψ)) C c hc hC h2
  exact creation_ibp_of_expGrowth i φ ψ hφ hψ (2 * C) c hc (by positivity)
    h0' hd' hA hB hD

/-- Iterated creation operators applied to the constant function one. -/
noncomputable def hermiteList : List ι → (ι → ℝ) → ℝ
  | [] => fun _ => 1
  | i :: l => creation i (hermiteList l)

/-- Every creation-operator Hermite function is smooth. -/
theorem contDiff_hermiteList (l : List ι) :
    ContDiff ℝ ⊤ (hermiteList l) := by
  induction l with
  | nil => simpa [hermiteList] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ι → ℝ => (1 : ℝ)))
  | cons i l ih =>
      have hcoord : ContDiff ℝ ⊤ (fun g : ι → ℝ => g i) := by fun_prop
      change ContDiff ℝ ⊤
        (fun g => g i * hermiteList l g - coordDeriv i (hermiteList l) g)
      exact (hcoord.mul ih).sub (contDiff_coordDeriv i ih)

/-- A fixed list containing each coordinate `i` exactly `α i` times. -/
noncomputable def multiIndexList (α : ι → ℕ) : List ι := by
  classical
  exact Finset.univ.toList.flatMap (fun i => List.replicate (α i) i)

omit [DecidableEq ι] in
/-- The iteration length is the total order of the multi-index. -/
theorem multiIndexList_length (α : ι → ℕ) :
    (multiIndexList α).length = ∑ i, α i := by
  classical
  simp [multiIndexList, List.length_flatMap]

noncomputable def partialMulti (α : ι → ℕ)
    (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  partialList (multiIndexList α) f

/-- The analytic conditions used along one specified list of coordinate
derivatives. At each step they concern only the next coordinate and the
current derivative of `f`; no derivative in an unrelated coordinate is
required. -/
def ExpIBPChain : List ι → ((ι → ℝ) → ℝ) → Prop
  | [], _ => True
  | i :: l, f =>
      ∃ C c : ℝ, 0 ≤ c ∧ 0 ≤ C ∧
          (∀ g, |hermiteList l g * f g| ≤
            C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) ∧
          (∀ g, |coordDeriv i (hermiteList l) g * f g| ≤
            C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) ∧
          (∀ g, |hermiteList l g * coordDeriv i f g| ≤
            C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) ∧
          ExpIBPChain l (coordDeriv i f)

/-- Multi-coordinate Gaussian IBP from exponential bounds along precisely
the derivative chain used by the multi-index. -/
theorem hermiteList_ibp_of_expChain (l : List ι)
    {f : (ι → ℝ) → ℝ} (hfSmooth : ContDiff ℝ l.length f)
    (hf : ExpIBPChain l f) :
    (∫ g, hermiteList l g * f g
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, partialList l f g
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  induction l generalizing f with
  | nil => simp [hermiteList, partialList]
  | cons i l ih =>
      rcases hf with ⟨C, c, hc, hC, h0, h1, h2, htail⟩
      have hfOrder : ContDiff ℝ (l.length + 1) f := by
        simpa [List.length_cons] using hfSmooth
      have hψ : ContDiff ℝ 1 f := hfOrder.of_le (by norm_num)
      have hφ : ContDiff ℝ 1 (hermiteList l) :=
        (contDiff_hermiteList l).of_le (by norm_num)
      calc
        (∫ g, hermiteList (i :: l) g * f g
          ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
            ∫ g, hermiteList l g * coordDeriv i f g
              ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
                simpa [hermiteList] using
                  creation_ibp_of_expProductBounds i (hermiteList l) f
                    hφ hψ C c hc hC h0 h1 h2
        _ = ∫ g, partialList l (coordDeriv i f) g
              ∂(Measure.pi fun _ : ι => gaussianReal 0 1) :=
          ih (contDiff_coordDeriv_succ i l.length hfOrder) htail
        _ = ∫ g, partialList (i :: l) f g
              ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := rfl

omit [Fintype ι] in
/-- A coordinate derivative of a polynomial depending on that coordinate alone. -/
theorem coordDeriv_aeval (i : ι) (p : Polynomial ℤ) (g : ι → ℝ) :
    coordDeriv i (fun h => Polynomial.aeval (h i) p) g =
      Polynomial.aeval (g i) (Polynomial.derivative p) := by
  classical
  simp [coordDeriv, Polynomial.deriv_aeval]

private def UpdateInvariant (i : ι) (f : (ι → ℝ) → ℝ) : Prop := by
  classical
  exact ∀ g x, f (Function.update g i x) = f g

omit [Fintype ι] in
private theorem coordDeriv_updateInvariant {i j : ι} (hij : i ≠ j)
    {f : (ι → ℝ) → ℝ} (hf : UpdateInvariant i f) :
    UpdateInvariant i (coordDeriv j f) := by
  classical
  intro g x
  unfold coordDeriv
  have hfun : (fun y => f (Function.update (Function.update g i x) j y)) =
      (fun y => f (Function.update g j y)) := by
    funext y
    rw [Function.update_comm hij x y g, hf (Function.update g j y) x]
  rw [hfun]
  simp [Function.update_of_ne hij.symm]

omit [Fintype ι] in
private theorem creation_updateInvariant {i j : ι} (hij : i ≠ j)
    {f : (ι → ℝ) → ℝ} (hf : UpdateInvariant i f) :
    UpdateInvariant i (creation j f) := by
  classical
  intro g x
  simp [creation, hf g x, coordDeriv_updateInvariant hij hf g x,
    Function.update_of_ne hij.symm]

omit [Fintype ι] in
private theorem hermiteList_updateInvariant (i : ι) (l : List ι)
    (hi : i ∉ l) : UpdateInvariant i (hermiteList l) := by
  induction l with
  | nil => intro g x; rfl
  | cons j l ih =>
      simp only [List.mem_cons, not_or] at hi
      exact creation_updateInvariant hi.1 (ih hi.2)

omit [Fintype ι] in
private theorem creation_aeval_mul_invariant (i : ι) (p : Polynomial ℤ)
    (q : (ι → ℝ) → ℝ) (hq : UpdateInvariant i q) (g : ι → ℝ) :
    creation i (fun h => Polynomial.aeval (h i) p * q h) g =
      (g i * Polynomial.aeval (g i) p -
        Polynomial.aeval (g i) (Polynomial.derivative p)) * q g := by
  classical
  have hfun : (fun x => Polynomial.aeval x p * q (Function.update g i x)) =
      (fun x => Polynomial.aeval x p * q g) := by
    funext x
    rw [hq g x]
  simp [creation, coordDeriv, hfun, Polynomial.deriv_aeval]
  ring

omit [Fintype ι] in
private theorem hermiteList_replicate_append (i : ι) (n : ℕ) (l : List ι)
    (hi : i ∉ l) (g : ι → ℝ) :
    hermiteList (List.replicate n i ++ l) g =
      Polynomial.aeval (g i) (Polynomial.hermite n) * hermiteList l g := by
  induction n generalizing g with
  | zero => simp [Polynomial.hermite_zero]
  | succ n ih =>
      change creation i (hermiteList (List.replicate n i ++ l)) g = _
      have hfun : hermiteList (List.replicate n i ++ l) =
          fun h => Polynomial.aeval (h i) (Polynomial.hermite n) * hermiteList l h := by
        funext h
        exact ih h
      rw [hfun, creation_aeval_mul_invariant i (Polynomial.hermite n)
        (hermiteList l) (hermiteList_updateInvariant i l hi) g,
        Polynomial.hermite_succ]
      simp [Polynomial.aeval_X, sub_mul]

omit [Fintype ι] in
private theorem hermiteList_flatMap_replicate (α : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (g : ι → ℝ) :
    hermiteList (l.flatMap (fun i => List.replicate (α i) i)) g =
      (l.map (fun i => Polynomial.aeval (g i) (Polynomial.hermite (α i)))).prod := by
  induction l generalizing g with
  | nil => simp [hermiteList]
  | cons i l ih =>
      obtain ⟨hil, hnodup⟩ := List.nodup_cons.mp hl
      have hnot : i ∉ l.flatMap (fun j => List.replicate (α j) j) := by
        intro h
        obtain ⟨j, hj, hij⟩ := List.mem_flatMap.mp h
        have heq : i = j := (List.mem_replicate.mp hij).2
        exact hil (heq ▸ hj)
      simp only [List.flatMap_cons, List.map_cons, List.prod_cons]
      rw [hermiteList_replicate_append i (α i)
        (l.flatMap (fun j => List.replicate (α j) j)) hnot g,
        ih hnodup g]

/-- Iterating the creation operators along `multiIndexList α` gives the product
`hermiteMulti α` of probabilists' Hermite polynomials. -/
theorem hermiteList_multiIndexList (α : ι → ℕ) :
    hermiteList (multiIndexList α) = hermiteMulti α := by
  classical
  funext g
  unfold hermiteMulti multiIndexList
  rw [hermiteList_flatMap_replicate α Finset.univ.toList
    (Finset.nodup_toList Finset.univ)]
  simp

omit [DecidableEq ι] in
/-- The multi-index Hermite product is continuous. -/
theorem continuous_hermiteMulti (α : ι → ℕ) : Continuous (hermiteMulti α) := by
  classical
  rw [← hermiteList_multiIndexList]
  exact (contDiff_hermiteList (multiIndexList α)).continuous

omit [DecidableEq ι] in
/-- The multi-index Hermite function itself has exponential growth. -/
theorem hermiteMulti_exp_bound (α : ι → ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ g : ι → ℝ,
      |hermiteMulti α g| ≤
        C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hermite_product_exp_bound α Finset.univ
  exact ⟨C, c, hC, hc, fun g => by simpa [hermiteMulti] using hb g⟩

omit [DecidableEq ι] in
/-- The left-hand side of the Hermite IBP formula is integrable under the
manuscript's exponential bound on `f`. -/
theorem integrable_hermiteMulti_mul_of_expGrowth (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (Cf : ℝ) (hCf : 0 ≤ Cf)
    (hfb : ∀ g, |f g| ≤
      Cf * Real.exp (Cf * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    Integrable (fun g => hermiteMulti α g * f g)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  obtain ⟨Ch, ch, hCh, hch, hhb⟩ := hermiteMulti_exp_bound α
  have hb : ∀ g, |hermiteMulti α g * f g| ≤
      (Ch * Cf) * Real.exp ((ch + Cf) *
        ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
    intro g
    rw [abs_mul]
    calc
      |hermiteMulti α g| * |f g| ≤
          (Ch * Real.exp (ch * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) *
            (Cf * Real.exp (Cf * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :=
        mul_le_mul (hhb g) (hfb g) (abs_nonneg _) (by positivity)
      _ = (Ch * Cf) * Real.exp ((ch + Cf) *
          ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
        rw [add_mul, Real.exp_add]
        ring
  exact integrable_of_euclidean_expBound _ ((continuous_hermiteMulti α).mul hf)
    (Ch * Cf) (ch + Cf) (by positivity) (by positivity) hb

/-- The exponential-growth chain yields the multi-index formula with the
standard product of probabilists' Hermite polynomials. -/
theorem hermiteMulti_ibp_of_expChain (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ}
    (hfSmooth : ContDiff ℝ (↑(∑ i : ι, α i)) f)
    (hf : ExpIBPChain (multiIndexList α) f) :
    (∫ g, (∏ i : ι, Polynomial.aeval (g i) (Polynomial.hermite (α i))) * f g
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, partialMulti α f g
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have horder : ContDiff ℝ (multiIndexList α).length f := by
    simpa only [multiIndexList_length] using hfSmooth
  simpa only [hermiteList_multiIndexList, hermiteMulti, partialMulti] using
    hermiteList_ibp_of_expChain (multiIndexList α) horder hf

/-- Coordinate derivatives commute for a twice continuously differentiable function. -/
theorem coordDeriv_comm (i j : ι) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    coordDeriv i (coordDeriv j f) = coordDeriv j (coordDeriv i f) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have he (k : ι) : coordDeriv k f = fun g => fderiv ℝ f g (Pi.single k 1) :=
    funext (coordDeriv_eq_fderiv k hf1)
  funext g
  rw [coordDeriv_eq_fderiv i (contDiff_coordDeriv_succ j 1 hf),
    coordDeriv_eq_fderiv j (contDiff_coordDeriv_succ i 1 hf), he i, he j]
  simp only [fderiv_clm_apply (hd.differentiable (by norm_num) g)
    (differentiableAt_const _), fderiv_const_apply, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- Reordering partial derivatives needs only as many derivatives as the list length. -/
theorem partialList_perm {l k : List ι} (hp : l.Perm k)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ l.length f) :
    partialList l f = partialList k f := by
  induction hp generalizing f with
  | nil => rfl
  | @cons i l k hp ih =>
      exact ih (contDiff_coordDeriv_succ i l.length hf)
  | swap i j l =>
      simp only [partialList]
      rw [coordDeriv_comm j i (hf.of_le (by
        exact_mod_cast (show 2 ≤ (j :: i :: l).length by simp)))]
  | trans hp hq ih ih' =>
      exact (ih hf).trans (ih' (by simpa only [← hp.length_eq] using hf))

/-- Each coordinate occurs with its prescribed multiplicity. -/
theorem multiIndexList_count (α : ι → ℕ) (i : ι) :
    (multiIndexList α).count i = α i := by
  classical
  simp [multiIndexList, List.count_flatMap, List.count_replicate]

/-- An ordered derivative list represents the multi-index given by its multiplicities. -/
theorem partialList_eq_partialMulti (l : List ι)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ l.length f) :
    partialList l f = partialMulti (fun i => l.count i) f := by
  apply partialList_perm _ hf
  exact List.perm_iff_count.mpr fun i => (multiIndexList_count (fun j => l.count j) i).symm

private def ExpBound (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ g,
    |f g| ≤ C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)

omit [DecidableEq ι] in
private theorem ExpBound.const (a : ℝ) : ExpBound (fun _ : ι → ℝ => a) := by
  exact ⟨|a|, 0, abs_nonneg _, le_rfl, by simp⟩

omit [DecidableEq ι] in
private theorem ExpBound.mul {f h : (ι → ℝ) → ℝ}
    (hf : ExpBound f) (hh : ExpBound h) : ExpBound (fun g => f g * h g) := by
  obtain ⟨C, c, hC, hc, hf⟩ := hf
  obtain ⟨D, d, hD, hd, hh⟩ := hh
  refine ⟨C * D, c + d, by positivity, by positivity, ?_⟩
  intro g
  rw [abs_mul]
  calc
    |f g| * |h g| ≤ (C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) *
        (D * Real.exp (d * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :=
      mul_le_mul (hf g) (hh g) (abs_nonneg _) (by positivity)
    _ = _ := by rw [add_mul, Real.exp_add]; ring

omit [DecidableEq ι] in
private theorem ExpBound.sub {f h : (ι → ℝ) → ℝ}
    (hf : ExpBound f) (hh : ExpBound h) : ExpBound (fun g => f g - h g) := by
  obtain ⟨C, c, hC, hc, hf⟩ := hf
  obtain ⟨D, d, hD, hd, hh⟩ := hh
  refine ⟨C + D, max c d, by positivity, by positivity, ?_⟩
  intro g
  have hfc := (hf g).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left c d) (norm_nonneg _))) hC)
  have hhd := (hh g).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right c d) (norm_nonneg _))) hD)
  exact (abs_sub _ _).trans (by nlinarith)

private inductive PolyFunction : ((ι → ℝ) → ℝ) → Prop
  | const (a : ℝ) : PolyFunction (fun _ => a)
  | coord (i : ι) : PolyFunction (fun g => g i)
  | sub {f h} : PolyFunction f → PolyFunction h → PolyFunction (fun g => f g - h g)
  | mul {f h} : PolyFunction f → PolyFunction h → PolyFunction (fun g => f g * h g)

omit [DecidableEq ι] in
private theorem PolyFunction.smooth {f : (ι → ℝ) → ℝ}
    (hf : PolyFunction f) : ContDiff ℝ ⊤ f := by
  induction hf with
  | const => fun_prop
  | coord => fun_prop
  | sub _ _ hf hh => exact hf.sub hh
  | mul _ _ hf hh => exact hf.mul hh

omit [DecidableEq ι] in
private theorem PolyFunction.expBound {f : (ι → ℝ) → ℝ}
    (hf : PolyFunction f) : ExpBound f := by
  induction hf with
  | const a => exact ExpBound.const a
  | coord i =>
      simpa [ExpBound, Polynomial.hermite_one] using hermite_factor_exp_bound (ι := ι) i 1
  | sub _ _ hf hh => exact hf.sub hh
  | mul _ _ hf hh => exact hf.mul hh

omit [Fintype ι] in
private theorem PolyFunction.deriv_closed [Finite ι] {f : (ι → ℝ) → ℝ}
    (hf : PolyFunction f) (i : ι) : PolyFunction (coordDeriv i f) := by
  have := Fintype.ofFinite ι
  induction hf with
  | const a =>
      change PolyFunction (fun g => deriv (fun _ : ℝ => a) (g i))
      simpa using (PolyFunction.const (ι := ι) 0)
  | coord j =>
      by_cases hij : j = i
      · subst j
        change PolyFunction (fun g => deriv (fun x => (Function.update g i x) i) (g i))
        simpa using (PolyFunction.const (ι := ι) 1)
      · change PolyFunction (fun g => deriv (fun x => (Function.update g i x) j) (g i))
        simpa [Function.update_of_ne hij] using (PolyFunction.const (ι := ι) 0)
  | @sub f h hf hh ihf ihh =>
      have he : coordDeriv i (fun g => f g - h g) =
          fun g => coordDeriv i f g - coordDeriv i h g := by
        funext g
        simp only [coordDeriv_eq_fderiv i ((hf.smooth.sub hh.smooth).of_le (by norm_num)),
          coordDeriv_eq_fderiv i (hf.smooth.of_le (by norm_num)),
          coordDeriv_eq_fderiv i (hh.smooth.of_le (by norm_num)),
          fderiv_fun_sub (hf.smooth.differentiable (by simp) g)
            (hh.smooth.differentiable (by simp) g), sub_apply]
      rw [he]
      exact ihf.sub ihh
  | @mul f h hf hh ihf ihh =>
      have he : coordDeriv i (fun g => f g * h g) =
          fun g => coordDeriv i f g * h g - (-(f g * coordDeriv i h g)) := by
        funext g
        rw [coordDeriv_mul i (hf.smooth.of_le (by norm_num))
          (hh.smooth.of_le (by norm_num))]
        ring
      rw [he]
      exact (ihf.mul hh).sub (by
        simpa using (PolyFunction.const 0).sub (hf.mul ihh))

omit [Fintype ι] in
private theorem polyFunction_hermiteList [Finite ι] (l : List ι) :
    PolyFunction (hermiteList l) := by
  have := Fintype.ofFinite ι
  induction l with
  | nil => exact PolyFunction.const 1
  | cons i l ih => exact ((PolyFunction.coord i).mul ih).sub (ih.deriv_closed i)

omit [DecidableEq ι] in
private theorem expBound_enlarge {f : (ι → ℝ) → ℝ} {C c D d : ℝ}
    (hC : 0 ≤ C) (hCD : C ≤ D) (hcd : c ≤ d)
    (hf : ∀ g, |f g| ≤ C * Real.exp (c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    ∀ g, |f g| ≤ D * Real.exp (d * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
  intro g
  exact (hf g).trans (mul_le_mul hCD
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcd (norm_nonneg _)))
    (Real.exp_nonneg _) (hC.trans hCD))

private theorem expIBPChain_of_prefix_bounds (l : List ι) {f : (ι → ℝ) → ℝ}
    (hb : ∀ p : List ι, p.IsPrefix l → ExpBound (partialList p f)) :
    ExpIBPChain l f := by
  induction l generalizing f with
  | nil => trivial
  | cons i l ih =>
      have hf : ExpBound f := hb [] (by simp)
      have hd : ExpBound (coordDeriv i f) := hb [i] (by simp)
      have hp := polyFunction_hermiteList l
      obtain ⟨C₀, c₀, hC₀, hc₀, h₀⟩ := hp.expBound.mul hf
      obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := (hp.deriv_closed i).expBound.mul hf
      obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := hp.expBound.mul hd
      refine ⟨C₀ + C₁ + C₂, c₀ + c₁ + c₂, by positivity, by positivity,
        expBound_enlarge hC₀ (by linarith) (by linarith) h₀,
        expBound_enlarge hC₁ (by linarith) (by linarith) h₁,
        expBound_enlarge hC₂ (by linarith) (by linarith) h₂, ?_⟩
      apply ih
      intro p hp
      exact hb (i :: p) (by simpa using hp)

/-- `lem:Gaussian-Hermite-IBP`: only the partial derivatives indexed by
`η ≤ α` need exponential growth, and finite smoothness of order `|α|` suffices. -/
theorem hermiteMulti_ibp_of_expGrowth (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(∑ i : ι, α i)) f)
    (hgrowth : ∀ η : ι → ℕ, η ≤ α → ∃ C : ℝ, 0 < C ∧ ∀ g,
      |partialMulti η f g| ≤ C * Real.exp (C * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    (∫ g, (∏ i : ι, Polynomial.aeval (g i) (Polynomial.hermite (α i))) * f g
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, partialMulti α f g ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  apply hermiteMulti_ibp_of_expChain α hf
  apply expIBPChain_of_prefix_bounds
  intro p hp
  have hcount : (fun i => p.count i) ≤ α := by
    intro i
    rw [← multiIndexList_count α i]
    exact hp.sublist.count_le i
  obtain ⟨C, hC, hb⟩ := hgrowth (fun i => p.count i) hcount
  have hsmooth : ContDiff ℝ p.length f := hf.of_le (by
    exact_mod_cast (hp.length_le.trans_eq (multiIndexList_length α)))
  rw [partialList_eq_partialMulti p hsmooth]
  exact ⟨C, C, hC.le, hC.le, hb⟩

/-- Both expectations in `lem:Gaussian-Hermite-IBP` are genuine integrals
under the manuscript's assumptions, including when `α = 0`. -/
theorem hermiteMulti_ibp_integrable (α : ι → ℕ)
    {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(∑ i : ι, α i)) f)
    (hgrowth : ∀ η : ι → ℕ, η ≤ α → ∃ C : ℝ, 0 < C ∧ ∀ g,
      |partialMulti η f g| ≤ C * Real.exp (C * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖)) :
    Integrable (fun g => (∏ i : ι, Polynomial.aeval (g i) (Polynomial.hermite (α i))) * f g)
      (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
    Integrable (partialMulti α f) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  obtain ⟨C₀, hC₀, h₀⟩ := hgrowth 0 (by simp)
  have hzero : partialMulti (0 : ι → ℕ) f = f := by
    have hnil : ∀ l : List ι, l.flatMap (fun _ => ([] : List ι)) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ l ih => simp [ih]
    simp [partialMulti, multiIndexList, hnil, partialList]
  rw [hzero] at h₀
  obtain ⟨C, hC, hb⟩ := hgrowth α le_rfl
  have hd : Continuous (partialMulti α f) := by
    apply (contDiff_partialList (multiIndexList α) 0 _).continuous
    simpa [multiIndexList_length] using hf
  constructor
  · simpa only [hermiteMulti] using
      integrable_hermiteMulti_mul_of_expGrowth α hf.continuous C₀ hC₀.le h₀
  · exact integrable_of_euclidean_expBound _ hd C C hC.le hC.le hb

omit [Fintype ι] in
private theorem polyFunction_partialList [Finite ι] (l : List ι) {f : (ι → ℝ) → ℝ}
    (hf : PolyFunction f) : PolyFunction (partialList l f) := by
  have := Fintype.ofFinite ι
  induction l generalizing f with
  | nil => exact hf
  | cons i l ih => exact ih (hf.deriv_closed i)

/-- Integration by parts for the pairing of two multivariate Hermite
functions. Their polynomial structure supplies all growth hypotheses. -/
theorem hermiteMulti_pair_ibp (α β : ι → ℕ) :
    (∫ g, hermiteMulti α g * hermiteMulti β g
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ g, partialMulti α (hermiteMulti β) g
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hβ : PolyFunction (hermiteMulti β) := by
    rw [← hermiteList_multiIndexList]
    exact polyFunction_hermiteList (multiIndexList β)
  have hdiff : ContDiff ℝ (↑(∑ i : ι, α i)) (hermiteMulti β) :=
    hβ.smooth.of_le (by simp)
  have hgrowth : ∀ η : ι → ℕ, η ≤ α → ∃ D : ℝ, 0 < D ∧ ∀ g,
      |partialMulti η (hermiteMulti β) g| ≤
        D * Real.exp (D * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖) := by
    intro η _
    obtain ⟨C, c, hC, hc, hb⟩ :=
      (polyFunction_partialList (multiIndexList η) hβ).expBound
    let D := max C c + 1
    have hD : 0 < D := by dsimp [D]; positivity
    refine ⟨D, hD, ?_⟩
    simpa only [partialMulti] using
      expBound_enlarge hC (by dsimp [D]; linarith [le_max_left C c])
        (by dsimp [D]; linarith [le_max_right C c]) hb
  simpa only [hermiteMulti] using
    hermiteMulti_ibp_of_expGrowth α hdiff hgrowth

end SYK.GaussianChaos
