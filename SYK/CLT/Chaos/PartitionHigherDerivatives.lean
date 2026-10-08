import SYK.CLT.Chaos.PartitionDerivatives

/-!
# Higher derivatives of the finite SYK partition function

The checked iterated trace-exponential derivative bound is transported to
`Setting.Z`, including its coupling scale, real part, smoothness, and Gaussian
growth. Entry points: `Setting.abs_partialMulti_Z_le`,
`Setting.hermite_coefficient_Z_eq_integral_partialMulti`, and
`Setting.abs_inner_hermiteLp_YGaussianLp_le`.
-/

open MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator InnerProductSpace

open SYK.GaussianChaos

namespace SYK.CLT

local instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (gaussianCouplings ι) := by
  unfold gaussianCouplings
  infer_instance

theorem partialList_cons_perm_append {ι : Type*} (i : ι) (l : List ι) :
    (i :: l).Perm (l ++ [i]) := by
  induction l with
  | nil => simp
  | cons j l ih =>
      exact (List.Perm.swap i j l).symm.trans (List.Perm.cons j ih)

theorem contDiff_partialList_top
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List ι) {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (GaussianConcentration.partialList l f) := by
  induction l generalizing f with
  | nil => simpa [GaussianConcentration.partialList] using hf
  | cons i l ih =>
      simpa [GaussianConcentration.partialList] using
        ih (GaussianConcentration.contDiff_coordDeriv i hf)

open MatrixAnalysis.DirectionalDerivative in
theorem partialList_eq_iterDirectionalFDeriv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List ι) {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f) :
    GaussianConcentration.partialList l f =
      iterDirectionalFDeriv f (l.map fun i => Pi.single i 1) := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
      have hperm : (i :: l).Perm (l ++ [i]) := by
        exact partialList_cons_perm_append i l
      rw [GaussianConcentration.partialList_perm hperm
        (hf.of_le (by simp)), GaussianConcentration.partialList_append]
      simp only [GaussianConcentration.partialList, List.map_cons,
        iterDirectionalFDeriv]
      have hsmooth : ContDiff ℝ ⊤ (GaussianConcentration.partialList l f) :=
        contDiff_partialList_top l hf
      funext x
      rw [GaussianConcentration.coordDeriv_eq_fderiv i (hsmooth.of_le (by norm_num)),
        ih hf]

open MatrixAnalysis.DirectionalDerivative in
theorem contDiff_iterDirectionalFDeriv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ⊤ f) (dirs : List E) :
    ContDiff ℝ ⊤ (iterDirectionalFDeriv f dirs) := by
  induction dirs generalizing f with
  | nil => simpa [iterDirectionalFDeriv] using hf
  | cons v dirs ih =>
      have htail := ih f hf
      have hfd : ContDiff ℝ ⊤ (fderiv ℝ (iterDirectionalFDeriv f dirs)) :=
        htail.fderiv_right (by simp)
      simpa [iterDirectionalFDeriv] using hfd.clm_apply contDiff_const

open MatrixAnalysis.DirectionalDerivative in
theorem iterDirectionalFDeriv_comp_right
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (hf : ContDiff ℝ ⊤ f) (L : G →L[ℝ] E)
    (dirs : List G) (x : G) :
    iterDirectionalFDeriv (f ∘ L) dirs x =
      iterDirectionalFDeriv f (dirs.map L) (L x) := by
  induction dirs generalizing f x with
  | nil => rfl
  | cons v dirs ih =>
      simp only [iterDirectionalFDeriv, List.map_cons]
      rw [show (fun y => iterDirectionalFDeriv (f ∘ L) dirs y) =
          (fun y => iterDirectionalFDeriv f (dirs.map L) (L y)) from
        funext fun y => ih f hf y]
      have htail : ContDiff ℝ ⊤ (iterDirectionalFDeriv f (dirs.map L)) :=
        contDiff_iterDirectionalFDeriv f hf (dirs.map L)
      change (fderiv ℝ (iterDirectionalFDeriv f (dirs.map L) ∘ L) x) v = _
      rw [fderiv_comp x (htail.differentiable (by simp) (L x)) L.differentiableAt]
      simp

open MatrixAnalysis.DirectionalDerivative in
theorem iterDirectionalFDeriv_comp_left
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (f : E → F) (hf : ContDiff ℝ ⊤ f)
    (dirs : List E) (x : E) :
    iterDirectionalFDeriv (L ∘ f) dirs x =
      L (iterDirectionalFDeriv f dirs x) := by
  induction dirs generalizing f x with
  | nil => rfl
  | cons v dirs ih =>
      simp only [iterDirectionalFDeriv]
      rw [show (fun y => iterDirectionalFDeriv (L ∘ f) dirs y) =
          (fun y => L (iterDirectionalFDeriv f dirs y)) from
        funext fun y => ih f hf y]
      have htail : ContDiff ℝ ⊤ (iterDirectionalFDeriv f dirs) :=
        contDiff_iterDirectionalFDeriv f hf dirs
      change (fderiv ℝ (L ∘ iterDirectionalFDeriv f dirs) x) v = _
      rw [fderiv_comp x L.differentiableAt (htail.differentiable (by simp) x)]
      simp

theorem normalizedHamiltonian_single
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Params) (M : MajoranaSystem P.N (Matrix d d ℂ))
    (I : InteractionIndex P.N P.q) :
    normalizedHamiltonian P M (PiLp.single 2 I 1) =
      couplingScale P • M.interactionOperator I := by
  classical
  simp [normalizedHamiltonian, hamiltonian, PiLp.single_apply]

theorem Setting.disorderMatrix_single {q : ℕ} (S : Setting q) (n : ℕ)
    (I : InteractionIndex (S.N n) q) :
    S.disorderMatrix n (PiLp.single 2 I 1) =
      couplingScale (S.params n) • (S.majorana n).interactionOperator I := by
  rw [S.disorderMatrix_apply]
  exact normalizedHamiltonian_single (S.params n) (S.majorana n) I

theorem norm_interactionOperator
    {N q : ℕ} {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (M : MajoranaSystem N (Matrix d d ℂ)) (hq : Even q)
    (I : InteractionIndex N q) :
    ‖M.interactionOperator I‖ = 1 := by
  apply CStarRing.norm_of_mem_unitary
  change star (M.interactionOperator I) * M.interactionOperator I = 1 ∧
    M.interactionOperator I * star (M.interactionOperator I) = 1
  rw [M.interactionOperator_star hq, M.interactionOperator_sq hq]
  exact ⟨rfl, rfl⟩

theorem Setting.norm_disorderMatrix_single {q : ℕ} (S : Setting q) (n : ℕ)
    (I : InteractionIndex (S.N n) q) :
    ‖S.disorderMatrix n (PiLp.single 2 I 1)‖ = couplingScale (S.params n) := by
  rw [S.disorderMatrix_single, norm_smul,
    norm_interactionOperator (S.majorana n) S.q_even I]
  simp [abs_of_nonneg (couplingScale_nonneg (S.params n))]

open MatrixAnalysis.DirectionalDerivative in
theorem Setting.iterDirectionalFDeriv_Z_eq {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (dirs : List (CouplingSpace (S.N n) q))
    (g : CouplingSpace (S.N n) q) :
    iterDirectionalFDeriv (S.Z β n) dirs g =
      (iterDirectionalFDeriv MatrixAnalysis.Matrix.traceExp
        (dirs.map fun v => (-β) • S.disorderMatrix n v)
        ((-β) • S.disorderMatrix n g)).re := by
  let T : Matrix (S.d n) (S.d n) ℂ → ℂ := MatrixAnalysis.Matrix.traceExp
  let L : CouplingSpace (S.N n) q →L[ℝ] Matrix (S.d n) (S.d n) ℂ :=
    (-β) • S.disorderMatrix n
  have hT : ContDiff ℝ ⊤ T := MatrixAnalysis.Matrix.contDiff_traceExp
  have heq : S.Z β n = (Complex.reCLM ∘ T) ∘ L := by
    funext x
    exact S.Z_eq_traceExp β n x
  rw [heq, iterDirectionalFDeriv_comp_right (Complex.reCLM ∘ T)
    (Complex.reCLM.contDiff.comp hT) L,
    iterDirectionalFDeriv_comp_left Complex.reCLM T hT]
  rfl

open MatrixAnalysis.DirectionalDerivative in
theorem Setting.abs_iterDirectionalFDeriv_Z_le {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (dirs : List (CouplingSpace (S.N n) q))
    (g : CouplingSpace (S.N n) q) :
    |iterDirectionalFDeriv (S.Z β n) dirs g| ≤
      (dirs.map fun v => |β| * ‖S.disorderMatrix n v‖).prod * S.Z β n g := by
  have hprod :
      ((dirs.map fun v => (-β) • S.disorderMatrix n v).map fun B => ‖B‖).prod =
        (dirs.map fun v => |β| * ‖S.disorderMatrix n v‖).prod := by
    induction dirs with
    | nil => rfl
    | cons v dirs ih =>
        simp only [List.map_cons, List.prod_cons]
        rw [norm_smul, Real.norm_eq_abs, abs_neg, ih]
  rw [S.iterDirectionalFDeriv_Z_eq]
  have hA : ((-β) • S.disorderMatrix n g).IsHermitian := by
    change star ((-β) • S.disorderMatrix n g) = (-β) • S.disorderMatrix n g
    simp [S.disorderMatrix_apply, normalizedHamiltonian_self_adjoint]
  have hb := MatrixAnalysis.Matrix.iterDirectionalFDeriv_traceExp_bound
    ((-β) • S.disorderMatrix n g) hA
    (dirs.map fun v => (-β) • S.disorderMatrix n v)
  calc
    _ ≤ ‖MatrixAnalysis.DirectionalDerivative.iterDirectionalFDeriv
        MatrixAnalysis.Matrix.traceExp
        (dirs.map fun v => (-β) • S.disorderMatrix n v)
        ((-β) • S.disorderMatrix n g)‖ := Complex.abs_re_le_norm _
    _ ≤ ((dirs.map fun v => (-β) • S.disorderMatrix n v).map fun B => ‖B‖).prod *
        ‖MatrixAnalysis.Matrix.traceExp ((-β) • S.disorderMatrix n g)‖ := hb
    _ = _ := by
      rw [S.norm_traceExp_disorder, hprod]

theorem Setting.abs_partialList_Z_le {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (l : List (InteractionIndex (S.N n) q))
    (g : InteractionIndex (S.N n) q → ℝ) :
    |GaussianConcentration.partialList l
        (fun x => S.Z β n (WithLp.toLp 2 x)) g| ≤
      (|β| * couplingScale (S.params n)) ^ l.length *
        S.Z β n (WithLp.toLp 2 g) := by
  let e :=
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : InteractionIndex (S.N n) q => ℝ)).symm
  have hF : ContDiff ℝ ⊤ (fun x : InteractionIndex (S.N n) q → ℝ =>
      S.Z β n (WithLp.toLp 2 x)) := S.Z_contDiff_pi β n
  rw [partialList_eq_iterDirectionalFDeriv l hF]
  change |MatrixAnalysis.DirectionalDerivative.iterDirectionalFDeriv
      (S.Z β n ∘ e.toContinuousLinearMap) (l.map fun i => Pi.single i 1) g| ≤ _
  rw [iterDirectionalFDeriv_comp_right (S.Z β n)
    (S.Z_contDiff_couplings β n) e.toContinuousLinearMap]
  have hprod :
      ((((l.map fun i => Pi.single i 1).map e.toContinuousLinearMap).map
        fun v => |β| * ‖S.disorderMatrix n v‖).prod) =
        (|β| * couplingScale (S.params n)) ^ l.length := by
    induction l with
    | nil => simp
    | cons i l ih =>
        simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
        have hei : e.toContinuousLinearMap (Pi.single i 1) =
            PiLp.single 2 i 1 := rfl
        rw [hei, S.norm_disorderMatrix_single, ih]
        ring
  have hb := S.abs_iterDirectionalFDeriv_Z_le β n
    ((l.map fun i => Pi.single i 1).map e.toContinuousLinearMap) (e g)
  rw [hprod] at hb
  have heg : e g = WithLp.toLp 2 g := rfl
  rw [heg] at hb
  exact hb

theorem Setting.abs_partialMulti_Z_le {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (α : InteractionIndex (S.N n) q → ℕ)
    (g : InteractionIndex (S.N n) q → ℝ) :
    |GaussianConcentration.partialMulti α
        (fun x => S.Z β n (WithLp.toLp 2 x)) g| ≤
      (|β| * couplingScale (S.params n)) ^ (∑ I, α I) *
        S.Z β n (WithLp.toLp 2 g) := by
  unfold GaussianConcentration.partialMulti
  simpa only [GaussianConcentration.multiIndexList_length] using
    S.abs_partialList_Z_le β n (GaussianConcentration.multiIndexList α) g

theorem Setting.partialMulti_Z_exp_growth {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (α : InteractionIndex (S.N n) q → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : InteractionIndex (S.N n) q → ℝ,
      |GaussianConcentration.partialMulti α
          (fun x => S.Z β n (WithLp.toLp 2 x)) g| ≤
        C * Real.exp (C * ‖WithLp.toLp 2 g‖) := by
  obtain ⟨c, hc, hZ⟩ := S.exists_Z_exp_bound_all_beta n
  let A := (|β| * couplingScale (S.params n)) ^ (∑ I, α I)
  let cβ := c * |β|
  let C := A + cβ + 1
  have hA : 0 ≤ A := pow_nonneg
    (mul_nonneg (abs_nonneg β) (couplingScale_nonneg (S.params n))) _
  have hcβ : 0 ≤ cβ := mul_nonneg hc (abs_nonneg β)
  refine ⟨C, by dsimp [C]; linarith, fun g => ?_⟩
  calc
    _ ≤ A * S.Z β n (WithLp.toLp 2 g) := S.abs_partialMulti_Z_le β n α g
    _ ≤ A * Real.exp (cβ * ‖WithLp.toLp 2 g‖) := by
      apply mul_le_mul_of_nonneg_left _ hA
      simpa only [cβ, mul_assoc] using hZ β (WithLp.toLp 2 g)
    _ ≤ C * Real.exp (C * ‖WithLp.toLp 2 g‖) := by
      apply mul_le_mul (by dsimp [C]; linarith)
        (Real.exp_le_exp.mpr (by
          apply mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)))
        (Real.exp_nonneg _) (by dsimp [C]; linarith)

theorem Setting.hermite_coefficient_Z_eq_integral_partialMulti
    {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (α : InteractionIndex (S.N n) q → ℕ) :
    (∫ g, hermiteMulti α g * S.Z β n (WithLp.toLp 2 g)
      ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
      ∫ g, GaussianConcentration.partialMulti α
        (fun x => S.Z β n (WithLp.toLp 2 x)) g
      ∂gaussianCouplings (InteractionIndex (S.N n) q) := by
  apply hermite_coefficient_ibp α
    ((S.Z_contDiff_pi β n).of_le (by simp))
  intro η _
  exact S.partialMulti_Z_exp_growth β n η

theorem Setting.integral_Z_pi {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    (∫ g : InteractionIndex (S.N n) q → ℝ,
      S.Z β n (WithLp.toLp 2 g)
        ∂gaussianCouplings (InteractionIndex (S.N n) q)) = S.meanZ β n := by
  let ι := InteractionIndex (S.N n) q
  let F : CouplingSpace (S.N n) q → ℝ := S.Z β n
  change (∫ g, F (WithLp.toLp 2 g) ∂gaussianCouplings ι) =
    ∫ g, F g ∂((gaussianCouplings ι).map (MeasurableEquiv.toLp 2 (ι → ℝ)))
  rw [integral_map_equiv (MeasurableEquiv.toLp 2 (ι → ℝ)) F]
  rfl

theorem Setting.abs_integral_Z_mul_hermite_le
    {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (α : InteractionIndex (S.N n) q → ℕ) :
    |∫ g, S.Z β n (WithLp.toLp 2 g) * hermiteMulti α g
      ∂gaussianCouplings (InteractionIndex (S.N n) q)| ≤
      (|β| * couplingScale (S.params n)) ^ (∑ I, α I) * S.meanZ β n := by
  let F := fun g : InteractionIndex (S.N n) q → ℝ =>
    S.Z β n (WithLp.toLp 2 g)
  have hgrowth : ∀ η : InteractionIndex (S.N n) q → ℕ, η ≤ α →
      ∃ C : ℝ, 0 < C ∧ ∀ g,
        |GaussianConcentration.partialMulti η F g| ≤
          C * Real.exp (C * ‖WithLp.toLp 2 g‖) := by
    intro η _
    exact S.partialMulti_Z_exp_growth β n η
  have hi := hermite_coefficient_integrable α
    ((S.Z_contDiff_pi β n).of_le (by simp)) hgrowth
  have hcoeff := S.hermite_coefficient_Z_eq_integral_partialMulti β n α
  have hcomm : (∫ g, S.Z β n (WithLp.toLp 2 g) * hermiteMulti α g
      ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
      ∫ g, hermiteMulti α g * S.Z β n (WithLp.toLp 2 g)
      ∂gaussianCouplings (InteractionIndex (S.N n) q) := by
    apply integral_congr_ae
    filter_upwards [] with g
    ring
  rw [hcomm, hcoeff]
  let A := (|β| * couplingScale (S.params n)) ^ (∑ I, α I)
  have hA : 0 ≤ A := pow_nonneg
    (mul_nonneg (abs_nonneg β) (couplingScale_nonneg (S.params n))) _
  have hZint : Integrable F
      (gaussianCouplings (InteractionIndex (S.N n) q)) :=
    (S.ZGaussian_memLp β n).integrable (by norm_num)
  calc
    _ ≤ ∫ g, |GaussianConcentration.partialMulti α F g|
        ∂gaussianCouplings (InteractionIndex (S.N n) q) := abs_integral_le_integral_abs
    _ ≤ ∫ g, A * F g
        ∂gaussianCouplings (InteractionIndex (S.N n) q) := by
      apply integral_mono hi.2.norm (hZint.const_mul A)
      intro g
      exact S.abs_partialMulti_Z_le β n α g
    _ = A * S.meanZ β n := by
      rw [integral_const_mul, S.integral_Z_pi]

theorem Setting.inner_hermiteLp_ZGaussianLp_eq_integral
    {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (α : InteractionIndex (S.N n) q → ℕ) :
    ⟪hermiteLp α, S.ZGaussianLp β n⟫_ℝ =
      ∫ g, S.Z β n (WithLp.toLp 2 g) * hermiteMulti α g
        ∂gaussianCouplings (InteractionIndex (S.N n) q) := by
  rw [MeasureTheory.L2.inner_def]
  have ha := (hermiteMulti_memLp_two α).coeFn_toLp
  have hb := (S.ZGaussian_memLp β n).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [ha, hb] with g ha' hb'
  change (S.ZGaussianLp β n) g * (hermiteLp α) g = _
  rw [show (hermiteLp α) g = hermiteMulti α g from ha',
    show (S.ZGaussianLp β n) g = S.Z β n (WithLp.toLp 2 g) from hb']

theorem Setting.abs_inner_hermiteLp_YGaussianLp_le
    {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ)
    (α : InteractionIndex (S.N n) q → ℕ) :
    |⟪hermiteLp α, S.YGaussianLp β n⟫_ℝ| ≤
      (|β| * couplingScale (S.params n)) ^ (∑ I, α I) := by
  rw [Setting.YGaussianLp, inner_smul_right,
    S.inner_hermiteLp_ZGaussianLp_eq_integral]
  have hmean : 0 < S.meanZ β n := (S.partition_moments β n).2.2
  have hcoeff := S.abs_integral_Z_mul_hermite_le β n α
  rw [abs_mul, abs_inv, abs_of_pos hmean]
  calc
    (S.meanZ β n)⁻¹ *
        |∫ g, S.Z β n (WithLp.toLp 2 g) * hermiteMulti α g
          ∂gaussianCouplings (InteractionIndex (S.N n) q)| ≤
      (S.meanZ β n)⁻¹ *
        ((|β| * couplingScale (S.params n)) ^ (∑ I, α I) * S.meanZ β n) :=
          mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = _ := by field_simp

end SYK.CLT
