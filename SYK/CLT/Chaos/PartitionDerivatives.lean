import SYK.Analysis.Matrix.TraceExpDerivatives
import SYK.CLT.Basic
import SYK.Probability.GaussianChaos.Basic
import SYK.Probability.GaussianChaos.HermiteIBP
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Finite partition-function derivatives

The first-order analytic inputs for `prop:exact-second-chaos` are proved for
the existing normalized model, at every real inverse temperature.
Entry points: `Setting.Z_contDiff_couplings`, `Setting.Z_hasDerivAt_beta`,
`Setting.coordDeriv_Z_eq`, `Setting.integral_Z_mul_sq_sub_one_ibp`,
`Setting.sum_integral_Y_mul_sq_sub_one`.
-/

open MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator

open SYK.GaussianChaos

namespace SYK.CLT

/-- The shared Hamiltonian, viewed with the matrix operator norm used by `Tool`. -/
noncomputable def Setting.disorderMatrix {q : ℕ} (S : Setting q) (n : ℕ) :
    CouplingSpace (S.N n) q →L[ℝ] Matrix (S.d n) (S.d n) ℂ :=
  (normalizedHamiltonianLinear (S.params n) (S.majorana n)).toLinearMap.toContinuousLinearMap

theorem Setting.disorderMatrix_apply {q : ℕ} (S : Setting q) (n : ℕ)
    (g : CouplingSpace (S.N n) q) :
    S.disorderMatrix n g = normalizedHamiltonian (S.params n) (S.majorana n) g := rfl

theorem Setting.Z_eq_traceExp {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) :
    S.Z β n g =
      (MatrixAnalysis.traceExp ((-β) • S.disorderMatrix n g)).re := by
  simp [Setting.Z, realPartitionFunction, partitionFunction, normalizedTrace,
    gibbsOperator, MatrixAnalysis.traceExp, MatrixAnalysis.normalizedTrace,
    Setting.disorderMatrix_apply, inv_mul_eq_div]

/-- Smoothness in the disorder, needed for finite Gaussian integration by parts. -/
theorem Setting.Z_contDiff_couplings {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    ContDiff ℝ ⊤ (S.Z β n) := by
  have ht : ContDiff ℝ ⊤
      (MatrixAnalysis.traceExp : Matrix (S.d n) (S.d n) ℂ → ℂ) :=
    MatrixAnalysis.contDiff_traceExp
  have h := Complex.reCLM.contDiff.comp (ht.comp
    ((contDiff_const : ContDiff ℝ ⊤ (fun _ : CouplingSpace (S.N n) q => (-β : ℝ))).smul
      (S.disorderMatrix n).contDiff))
  change ContDiff ℝ ⊤ (fun x =>
    (MatrixAnalysis.traceExp ((-β) • S.disorderMatrix n x)).re) at h
  simpa only [← S.Z_eq_traceExp] using h

/-- Scaling the disorder is the same as scaling the real inverse temperature. -/
theorem Setting.Z_smul {q : ℕ} (S : Setting q) (β t : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) :
    S.Z β n (t • g) = S.Z (t * β) n g := by
  simp only [S.Z_eq_traceExp, map_smul, smul_smul]
  congr 3
  ring

theorem Setting.norm_traceExp_disorder {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) :
    ‖MatrixAnalysis.traceExp ((-β) • S.disorderMatrix n g)‖ = S.Z β n g := by
  have heq : MatrixAnalysis.traceExp ((-β) • S.disorderMatrix n g) =
      (S.Z β n g : ℂ) := by
    apply Complex.ext
    · exact (S.Z_eq_traceExp β n g).symm
    · simpa [partitionFunction, normalizedTrace, gibbsOperator,
        MatrixAnalysis.traceExp, MatrixAnalysis.normalizedTrace,
        Setting.disorderMatrix_apply, inv_mul_eq_div, Complex.real_smul] using
        partitionFunction_im_eq_zero (S.params n) (S.majorana n) β g
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact le_trans (by norm_num) (S.Z_ge_one β n g)

/-- A first directional derivative bound, with no restriction on inverse temperature. -/
theorem Setting.norm_fderiv_Z_le {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (g v : CouplingSpace (S.N n) q) :
    ‖fderiv ℝ (S.Z β n) g v‖ ≤
      |β| * ‖S.disorderMatrix n v‖ * S.Z β n g := by
  let T : Matrix (S.d n) (S.d n) ℂ → ℂ := MatrixAnalysis.traceExp
  let L := (-β) • S.disorderMatrix n
  have ht : ContDiff ℝ ⊤ T := MatrixAnalysis.contDiff_traceExp
  have h := Complex.reCLM.hasFDerivAt.comp g
    ((ht.differentiable (by simp) (L g)).hasFDerivAt.comp g L.hasFDerivAt)
  have heq : (fun x => (T (L x)).re) = S.Z β n := by
    funext x
    exact (S.Z_eq_traceExp β n x).symm
  change HasFDerivAt (fun x => (T (L x)).re) _ g at h
  rw [heq] at h
  rw [h.fderiv]
  change ‖(fderiv ℝ T (L g) (L v)).re‖ ≤ _
  have hA : (L g).IsHermitian := by
    change star ((-β) • S.disorderMatrix n g) = (-β) • S.disorderMatrix n g
    simp [Setting.disorderMatrix_apply, normalizedHamiltonian_self_adjoint]
  have hb := MatrixAnalysis.iterDirectionalFDeriv_traceExp_bound
    (L g) hA [L v]
  simp only [MatrixAnalysis.DirectionalDerivative.iterDirectionalFDeriv,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hb
  calc
    _ ≤ ‖fderiv ℝ T (L g) (L v)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖L v‖ * ‖T (L g)‖ := hb
    _ = _ := by
      change ‖(-β) • S.disorderMatrix n v‖ *
        ‖MatrixAnalysis.traceExp ((-β) • S.disorderMatrix n g)‖ = _
      rw [S.norm_traceExp_disorder, norm_smul]
      simp

theorem Setting.Z_contDiff_beta {q : ℕ} (S : Setting q) (n : ℕ)
    (g : CouplingSpace (S.N n) q) : ContDiff ℝ ⊤ (fun β => S.Z β n g) := by
  have hg : ContDiff ℝ ⊤ (fun b : ℝ => b • g) := contDiff_id.smul contDiff_const
  have h := (S.Z_contDiff_couplings 1 n).comp hg
  simpa only [Function.comp_def, S.Z_smul, mul_one] using h

theorem Setting.Z_hasDerivAt_beta {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) :
    HasDerivAt (fun b => S.Z b n g) (fderiv ℝ (S.Z 1 n) (β • g) g) β := by
  have h := ((S.Z_contDiff_couplings 1 n).differentiable (by simp)
    (β • g)).hasFDerivAt.comp_hasDerivAt β ((hasDerivAt_id β).smul_const g)
  simpa only [Function.comp_def, S.Z_smul, mul_one, one_smul, id_eq] using h

/-- Euler's radial identity for the finite partition function. -/
theorem Setting.fderiv_Z_self_eq_beta_deriv {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (g : CouplingSpace (S.N n) q) :
    fderiv ℝ (S.Z β n) g g = β * deriv (fun b => S.Z b n g) β := by
  have hleft := ((S.Z_contDiff_couplings β n).differentiable (by simp)
    ((1 : ℝ) • g)).hasFDerivAt.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const g)
  have hright := ((S.Z_contDiff_beta n g).differentiable (by simp) (1 * β)).hasDerivAt.comp 1
    ((hasDerivAt_id (1 : ℝ)).mul_const β)
  simp only [one_smul, Function.comp_def] at hleft
  simp only [one_mul, Function.comp_def] at hright
  simp_rw [S.Z_smul] at hleft
  have h := hleft.unique hright
  simpa only [mul_comm] using h

theorem Setting.norm_deriv_Z_beta_le {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (g : CouplingSpace (S.N n) q) :
    ‖deriv (fun b => S.Z b n g) β‖ ≤ ‖S.disorderMatrix n g‖ * S.Z β n g := by
  rw [(S.Z_hasDerivAt_beta β n g).deriv]
  simpa only [abs_one, one_mul, S.Z_smul, mul_one] using
    S.norm_fderiv_Z_le 1 n (β • g) g

theorem Setting.continuous_deriv_Z_beta {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    Continuous (fun g : CouplingSpace (S.N n) q => deriv (fun b => S.Z b n g) β) := by
  have hg : Continuous (fun g : CouplingSpace (S.N n) q => β • g) :=
    continuous_id.const_smul β
  have h := ((S.Z_contDiff_couplings 1 n).continuous_fderiv (by simp)).comp hg
  have h' := h.clm_apply continuous_id
  have heq : (fun g : CouplingSpace (S.N n) q => deriv (fun b => S.Z b n g) β) =
      fun g => fderiv ℝ (S.Z 1 n) (β • g) g := by
    funext g
    exact (S.Z_hasDerivAt_beta β n g).deriv
  rw [heq]
  exact h'

/-- An exponential bound uniform on bounded inverse-temperature intervals. -/
theorem Setting.exists_Z_exp_bound_all_beta {q : ℕ} (S : Setting q) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (g : CouplingSpace (S.N n) q),
      S.Z β n g ≤ Real.exp (C * |β| * ‖g‖) := by
  obtain ⟨C, hC, hb⟩ := exists_realPartitionFunction_exp_bound (S.params n) (S.majorana n) 1
  refine ⟨C, hC, fun β g => ?_⟩
  have h : S.Z 1 n (β • g) ≤ Real.exp (C * ‖β • g‖) := hb (β • g)
  simpa only [S.Z_smul, mul_one, norm_smul, Real.norm_eq_abs, mul_assoc] using h

/-- Differentiating the finite Gaussian expectation is valid at every real temperature. -/
theorem Setting.meanZ_hasDerivAt {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    HasDerivAt (fun b => S.meanZ b n)
      (∫ g, deriv (fun b => S.Z b n g) β ∂standardGaussianMeasure (S.N n) q) β := by
  obtain ⟨C, hC, hb⟩ := S.exists_Z_exp_bound_all_beta n
  let K := ‖S.disorderMatrix n‖
  let c := C * (|β| + 1) + 1
  have hbound (g : CouplingSpace (S.N n) q) (b : ℝ) (hb' : b ∈ Metric.ball β 1) :
      ‖deriv (fun t => S.Z t n g) b‖ ≤ K * Real.exp (c * ‖g‖) := by
    have hab : |b| ≤ |β| + 1 := by
      have hd : |b - β| < 1 := by simpa [Real.dist_eq] using hb'
      have ha := abs_add_le (b - β) β
      rw [sub_add_cancel] at ha
      linarith
    have hnorm : ‖g‖ ≤ Real.exp ‖g‖ := by linarith [Real.add_one_le_exp ‖g‖]
    calc
      _ ≤ ‖S.disorderMatrix n g‖ * S.Z b n g := S.norm_deriv_Z_beta_le b n g
      _ ≤ (K * ‖g‖) * Real.exp (C * (|β| + 1) * ‖g‖) := by
        apply mul_le_mul ((S.disorderMatrix n).le_opNorm g)
          ((hb b g).trans (Real.exp_le_exp.mpr (by gcongr)))
          (by linarith [S.Z_ge_one b n g]) (by positivity)
      _ ≤ (K * Real.exp ‖g‖) * Real.exp (C * (|β| + 1) * ‖g‖) := by gcongr
      _ = K * Real.exp (c * ‖g‖) := by rw [mul_assoc, ← Real.exp_add]; congr 2; dsimp [c]; ring
  have hi : Integrable (fun g : CouplingSpace (S.N n) q => K * Real.exp (c * ‖g‖))
      (standardGaussianMeasure (S.N n) q) :=
    (GaussianConcentration.integrable_exp_mul_norm c).const_mul K
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b g => S.Z b n g) (F' := fun b g => deriv (fun t => S.Z t n g) b)
    (Metric.ball_mem_nhds β (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun b =>
      (S.Z_contDiff_couplings b n).continuous.aestronglyMeasurable)
    ((S.partition_moments β n).1.integrable (by norm_num))
    (S.continuous_deriv_Z_beta β n).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound) hi
    (Filter.Eventually.of_forall fun g b _ =>
      ((S.Z_contDiff_beta n g).differentiable (by simp) b).hasDerivAt)
  exact h.2

theorem Setting.Z_contDiff_pi {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    ContDiff ℝ ⊤ (fun g : InteractionIndex (S.N n) q → ℝ => S.Z β n (WithLp.toLp 2 g)) :=
  (S.Z_contDiff_couplings β n).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : InteractionIndex (S.N n) q => ℝ)).symm.contDiff

theorem Setting.coordDeriv_Z_eq {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (I : InteractionIndex (S.N n) q) (g : InteractionIndex (S.N n) q → ℝ) :
    coordDeriv I (fun x => S.Z β n (WithLp.toLp 2 x)) g =
      fderiv ℝ (S.Z β n) (WithLp.toLp 2 g) (PiLp.single 2 I 1) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : InteractionIndex (S.N n) q => ℝ)).symm
  have h := ((S.Z_contDiff_couplings β n).differentiable (by simp) (e g)).hasFDerivAt.comp g
    e.hasFDerivAt
  rw [coordDeriv_eq_fderiv I ((S.Z_contDiff_pi β n).of_le (by simp))]
  change (fderiv ℝ (S.Z β n ∘ e) g) (Pi.single I 1) = _
  rw [h.fderiv]
  rfl

/-- The value and each selected first partial derivative have exponential growth. -/
theorem Setting.Z_coord_exp_bounds {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧
      (∀ g : InteractionIndex (S.N n) q → ℝ,
        |S.Z β n (WithLp.toLp 2 g)| ≤ C * Real.exp (c * ‖WithLp.toLp 2 g‖)) ∧
      (∀ (I : InteractionIndex (S.N n) q) (g : InteractionIndex (S.N n) q → ℝ),
        |coordDeriv I (fun x => S.Z β n (WithLp.toLp 2 x)) g| ≤
          C * Real.exp (c * ‖WithLp.toLp 2 g‖)) := by
  obtain ⟨c, hc, hb⟩ := S.exists_Z_exp_bound_all_beta n
  let K := |β| * ‖S.disorderMatrix n‖
  have hK : 0 ≤ K := by positivity
  have hZ (g : InteractionIndex (S.N n) q → ℝ) :
      |S.Z β n (WithLp.toLp 2 g)| ≤ Real.exp ((c * |β|) * ‖WithLp.toLp 2 g‖) := by
    rw [abs_of_nonneg (le_trans (by norm_num) (S.Z_ge_one β n _))]
    exact hb β _
  refine ⟨K + 1, c * |β|, by positivity, by positivity, ?_, ?_⟩
  · intro g
    exact (hZ g).trans (le_mul_of_one_le_left (Real.exp_nonneg _) (by linarith))
  · intro I g
    rw [S.coordDeriv_Z_eq]
    have hv : ‖S.disorderMatrix n (PiLp.single 2 I 1)‖ ≤ ‖S.disorderMatrix n‖ := by
      simpa using (S.disorderMatrix n).le_opNorm (PiLp.single 2 I 1)
    calc
      _ ≤ |β| * ‖S.disorderMatrix n (PiLp.single 2 I 1)‖ * S.Z β n (WithLp.toLp 2 g) :=
        S.norm_fderiv_Z_le β n _ _
      _ ≤ K * Real.exp ((c * |β|) * ‖WithLp.toLp 2 g‖) := by
        dsimp [K]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hv (abs_nonneg β))
          (hb β _) (le_trans (by norm_num) (S.Z_ge_one β n _)) (by positivity)
      _ ≤ (K + 1) * Real.exp ((c * |β|) * ‖WithLp.toLp 2 g‖) := by gcongr; linarith

/-- First-order Gaussian IBP suffices for the diagonal quadratic coefficient. -/
theorem Setting.integral_Z_mul_sq_sub_one_ibp {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (I : InteractionIndex (S.N n) q) :
    (∫ g : InteractionIndex (S.N n) q → ℝ,
      S.Z β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
        ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
    ∫ g : InteractionIndex (S.N n) q → ℝ,
      g I * coordDeriv I (fun x => S.Z β n (WithLp.toLp 2 x)) g
        ∂gaussianCouplings (InteractionIndex (S.N n) q) := by
  let F := fun g : InteractionIndex (S.N n) q → ℝ => S.Z β n (WithLp.toLp 2 g)
  obtain ⟨C, c, hC, hc, hF, hd⟩ := S.Z_coord_exp_bounds β n
  have hcoord : coordDeriv I (fun g : InteractionIndex (S.N n) q → ℝ => g I) =
      fun _ => 1 := by
    funext g
    simp [coordDeriv]
  have hnorm (g : InteractionIndex (S.N n) q → ℝ) :
      |g I| ≤ Real.exp ‖WithLp.toLp 2 g‖ :=
    (PiLp.norm_apply_le (WithLp.toLp 2 g) I).trans
      (by linarith [Real.add_one_le_exp ‖WithLp.toLp 2 g‖])
  have hprod (g : InteractionIndex (S.N n) q → ℝ) (x : ℝ)
      (hx : |x| ≤ C * Real.exp (c * ‖WithLp.toLp 2 g‖)) :
      |g I * x| ≤ C * Real.exp ((c + 1) * ‖WithLp.toLp 2 g‖) := by
    rw [abs_mul]
    calc
      _ ≤ Real.exp ‖WithLp.toLp 2 g‖ * (C * Real.exp (c * ‖WithLp.toLp 2 g‖)) :=
        mul_le_mul (hnorm g) hx (abs_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have h := creation_ibp_of_expProductBounds I
    (fun g : InteractionIndex (S.N n) q → ℝ => g I) F
    (by fun_prop) ((S.Z_contDiff_pi β n).of_le (by simp)) C (c + 1)
    (by positivity) hC (fun g => hprod g _ (hF g))
    (fun g => by
      rw [hcoord, one_mul]
      exact (hF g).trans (by gcongr; linarith))
    (fun g => hprod g _ (hd I g))
  have heq : (fun g : InteractionIndex (S.N n) q → ℝ =>
      creation I (fun x => x I) g * F g) =
      fun g => F g * (g I ^ 2 - 1) := by
    funext g
    simp only [creation, hcoord]
    ring
  rw [heq] at h
  exact h

/-- The sum of the diagonal coefficients is the radial annealed derivative. -/
theorem Setting.sum_integral_Z_mul_sq_sub_one {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    (∑ I : InteractionIndex (S.N n) q,
      ∫ g : InteractionIndex (S.N n) q → ℝ,
        S.Z β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
          ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
      β * deriv (fun b => S.meanZ b n) β := by
  classical
  let F := fun g : InteractionIndex (S.N n) q → ℝ => S.Z β n (WithLp.toLp 2 g)
  obtain ⟨C, c, hC, hc, _, hd⟩ := S.Z_coord_exp_bounds β n
  have hi (I : InteractionIndex (S.N n) q) :
      Integrable (fun g => g I * coordDeriv I F g)
        (gaussianCouplings (InteractionIndex (S.N n) q)) := by
    have hcont : Continuous (coordDeriv I F) :=
      (contDiff_coordDeriv_succ I 0
        ((S.Z_contDiff_pi β n).of_le (by simp))).continuous
    exact integrable_coord_mul_of_euclidean_expBound _ hcont I C c hc hC
      (hd I)
  have hrad (g : InteractionIndex (S.N n) q → ℝ) :
      (∑ I, g I * coordDeriv I F g) =
        β * deriv (fun b => S.Z b n (WithLp.toLp 2 g)) β := by
    simp only [F, S.coordDeriv_Z_eq]
    rw [← S.fderiv_Z_self_eq_beta_deriv]
    have hg : (∑ I, g I • PiLp.single 2 I (1 : ℝ)) = WithLp.toLp 2 g := by
      ext I
      simp [Pi.single_apply]
    calc
      _ = fderiv ℝ (S.Z β n) (WithLp.toLp 2 g) (∑ I, g I • PiLp.single 2 I 1) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = _ := congrArg (fderiv ℝ (S.Z β n) (WithLp.toLp 2 g)) hg
  simp_rw [S.integral_Z_mul_sq_sub_one_ibp]
  rw [← integral_finsetSum _ (fun I _ => hi I)]
  change (∫ g, ∑ I, g I * coordDeriv I F g
    ∂gaussianCouplings (InteractionIndex (S.N n) q)) = _
  simp_rw [hrad]
  rw [integral_const_mul, (S.meanZ_hasDerivAt β n).deriv]
  congr 1
  change _ = ∫ g, deriv (fun b => S.Z b n g) β
    ∂((gaussianCouplings (InteractionIndex (S.N n) q)).map
      (MeasurableEquiv.toLp 2 (InteractionIndex (S.N n) q → ℝ)))
  rw [integral_map_equiv]
  rfl

/-- The normalized diagonal coefficient sum, including zero inverse temperature. -/
theorem Setting.sum_integral_Y_mul_sq_sub_one {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    (∑ I : InteractionIndex (S.N n) q,
      ∫ g : InteractionIndex (S.N n) q → ℝ,
        S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
          ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
      β * deriv (fun b => Real.log (S.meanZ b n)) β := by
  have hdiv (g : InteractionIndex (S.N n) q → ℝ) (I : InteractionIndex (S.N n) q) :
      S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1) =
        (S.Z β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)) / S.meanZ β n := by
    unfold Setting.Y
    ring
  simp_rw [hdiv, integral_div]
  rw [← Finset.sum_div, S.sum_integral_Z_mul_sq_sub_one]
  have hlog := (S.meanZ_hasDerivAt β n).log (S.partition_moments β n).2.2.ne'
  rw [hlog.deriv, (S.meanZ_hasDerivAt β n).deriv]
  ring

end SYK.CLT
