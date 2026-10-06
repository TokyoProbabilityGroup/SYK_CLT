import SYK.CLT.Lemmas.GaussianFourthMoment
import SYK.CLT.Basic

/-! # Fourth moments of independent finite sums -/

open MeasureTheory ProbabilityTheory

namespace SYK.CLT

private theorem integrable_pow_le_four {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 4 μ) (k : ℕ) (hk : k ≤ 4) :
    Integrable (fun ω => X ω ^ k) μ := by
  have hn := integrable_norm_pow_of_le hX.aestronglyMeasurable hk
    (hX.integrable_norm_pow (by decide : 4 ≠ 0))
  apply hn.mono' (hX.aestronglyMeasurable.pow k)
  filter_upwards [] with ω
  simp only [Pi.pow_apply, norm_pow, le_refl]

/-- The fourth-moment addition formula for independent centered variables. -/
theorem fourth_moment_add_of_indep {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (hXY : IndepFun X Y μ)
    (hXmean : (∫ ω, X ω ∂μ) = 0)
    (hYmean : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) =
      (∫ ω, X ω ^ 4 ∂μ) +
        6 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) +
        (∫ ω, Y ω ^ 4 ∂μ) := by
  have hX1 : Integrable X μ := by
    simpa using integrable_pow_le_four hX 1 (by decide)
  have hX2 := integrable_pow_le_four hX 2 (by decide)
  have hX3 := integrable_pow_le_four hX 3 (by decide)
  have hX4 := integrable_pow_le_four hX 4 (by decide)
  have hY1 : Integrable Y μ := by
    simpa using integrable_pow_le_four hY 1 (by decide)
  have hY2 := integrable_pow_le_four hY 2 (by decide)
  have hY3 := integrable_pow_le_four hY 3 (by decide)
  have hY4 := integrable_pow_le_four hY 4 (by decide)
  have hi31 : IndepFun (fun ω => X ω ^ 3) Y μ := by
    simpa only [Function.comp_def, id_eq] using
      hXY.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 3)) measurable_id
  have hi22 : IndepFun (fun ω => X ω ^ 2) (fun ω => Y ω ^ 2) μ := by
    simpa only [Function.comp_def] using
      hXY.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
        (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
  have hi13 : IndepFun X (fun ω => Y ω ^ 3) μ := by
    simpa only [Function.comp_def, id_eq] using
      hXY.comp measurable_id (by fun_prop : Measurable (fun x : ℝ => x ^ 3))
  have h31 : Integrable (fun ω => X ω ^ 3 * Y ω) μ := by
    change Integrable ((fun ω => X ω ^ 3) * Y) μ
    exact hi31.integrable_mul hX3 hY1
  have h22 : Integrable (fun ω => X ω ^ 2 * Y ω ^ 2) μ := by
    change Integrable ((fun ω => X ω ^ 2) * fun ω => Y ω ^ 2) μ
    exact hi22.integrable_mul hX2 hY2
  have h13 : Integrable (fun ω => X ω * Y ω ^ 3) μ := by
    change Integrable (X * fun ω => Y ω ^ 3) μ
    exact hi13.integrable_mul hX1 hY3
  have e31 : (∫ ω, X ω ^ 3 * Y ω ∂μ) = 0 := by
    have h := hi31.integral_mul_eq_mul_integral
      hX3.aestronglyMeasurable hY1.aestronglyMeasurable
    simpa only [Pi.mul_apply, hYmean, mul_zero] using h
  have e22 : (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ) =
      (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) := by
    simpa only [Pi.mul_apply] using hi22.integral_mul_eq_mul_integral
      hX2.aestronglyMeasurable hY2.aestronglyMeasurable
  have e13 : (∫ ω, X ω * Y ω ^ 3 ∂μ) = 0 := by
    have h := hi13.integral_mul_eq_mul_integral
      hX1.aestronglyMeasurable hY3.aestronglyMeasurable
    simpa only [Pi.mul_apply, hXmean, zero_mul] using h
  have hB : Integrable (fun ω => 4 * (X ω ^ 3 * Y ω)) μ := h31.const_mul 4
  have hC : Integrable (fun ω => 6 * (X ω ^ 2 * Y ω ^ 2)) μ := h22.const_mul 6
  have hD : Integrable (fun ω => 4 * (X ω * Y ω ^ 3)) μ := h13.const_mul 4
  have hAB := hX4.add hB
  have hABC := hAB.add hC
  have hABCD := hABC.add hD
  have hp (ω : Ω) : (X ω + Y ω) ^ 4 =
      X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
        6 * (X ω ^ 2 * Y ω ^ 2) +
        4 * (X ω * Y ω ^ 3) + Y ω ^ 4 := by ring
  calc
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) =
        ∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
          6 * (X ω ^ 2 * Y ω ^ 2) +
          4 * (X ω * Y ω ^ 3) + Y ω ^ 4 ∂μ := by
            congr 1
            funext ω
            exact hp ω
    _ = _ := by
      have eABCD :
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
            6 * (X ω ^ 2 * Y ω ^ 2) +
            4 * (X ω * Y ω ^ 3) + Y ω ^ 4 ∂μ) =
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
            6 * (X ω ^ 2 * Y ω ^ 2) +
            4 * (X ω * Y ω ^ 3) ∂μ) +
          (∫ ω, Y ω ^ 4 ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hABCD hY4
      have eABC :
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
            6 * (X ω ^ 2 * Y ω ^ 2) +
            4 * (X ω * Y ω ^ 3) ∂μ) =
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
            6 * (X ω ^ 2 * Y ω ^ 2) ∂μ) +
          (∫ ω, 4 * (X ω * Y ω ^ 3) ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hABC hD
      have eAB :
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
            6 * (X ω ^ 2 * Y ω ^ 2) ∂μ) =
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) ∂μ) +
          (∫ ω, 6 * (X ω ^ 2 * Y ω ^ 2) ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hAB hC
      have eA :
          (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) ∂μ) =
          (∫ ω, X ω ^ 4 ∂μ) +
          (∫ ω, 4 * (X ω ^ 3 * Y ω) ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hX4 hB
      rw [eABCD, eABC, eAB, eA]
      simp only [integral_const_mul, e31, e22, e13, mul_zero]
      ring

theorem second_moment_add_of_indep {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (hXY : IndepFun X Y μ)
    (hXmean : (∫ ω, X ω ∂μ) = 0)
    (_hYmean : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, (X ω + Y ω) ^ 2 ∂μ) =
      (∫ ω, X ω ^ 2 ∂μ) + (∫ ω, Y ω ^ 2 ∂μ) := by
  have hX1 : Integrable X μ := by
    simpa using integrable_pow_le_four hX 1 (by decide)
  have hY1 : Integrable Y μ := by
    simpa using integrable_pow_le_four hY 1 (by decide)
  have hX2 := integrable_pow_le_four hX 2 (by decide)
  have hY2 := integrable_pow_le_four hY 2 (by decide)
  have hXYint : Integrable (fun ω => X ω * Y ω) μ := by
    change Integrable (X * Y) μ
    exact hXY.integrable_mul hX1 hY1
  have eXY : (∫ ω, X ω * Y ω ∂μ) = 0 := by
    have h := hXY.integral_mul_eq_mul_integral
      hX1.aestronglyMeasurable hY1.aestronglyMeasurable
    simpa only [Pi.mul_apply, hXmean, zero_mul] using h
  have hp (ω : Ω) : (X ω + Y ω) ^ 2 =
      X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 := by ring
  have hB := hXYint.const_mul 2
  have hAB := hX2.add hB
  calc
    (∫ ω, (X ω + Y ω) ^ 2 ∂μ) =
        ∫ ω, X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 ∂μ := by
          congr 1
          funext ω
          exact hp ω
    _ = _ := by
      have eAB :
          (∫ ω, X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 ∂μ) =
          (∫ ω, X ω ^ 2 + 2 * (X ω * Y ω) ∂μ) +
          (∫ ω, Y ω ^ 2 ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hAB hY2
      have eA :
          (∫ ω, X ω ^ 2 + 2 * (X ω * Y ω) ∂μ) =
          (∫ ω, X ω ^ 2 ∂μ) +
          (∫ ω, 2 * (X ω * Y ω) ∂μ) := by
        simpa only [Pi.add_apply] using integral_add hX2 hB
      rw [eAB, eA]
      simp only [integral_const_mul, eXY, mul_zero, add_zero]

section GaussianSums

variable {ι : Type*} [Fintype ι]

local instance : IsProbabilityMeasure (gaussianCouplings ι) := by
  unfold gaussianCouplings
  infer_instance

private noncomputable def centeredSquareSum (s : Finset ι) (g : ι → ℝ) : ℝ :=
  ∑ i ∈ s, centeredGaussianSquare (g i)

private theorem centeredSquareCoordinate_memLp_four (i : ι) :
    MemLp (fun g : ι → ℝ => centeredGaussianSquare (g i)) 4
      (gaussianCouplings ι) := by
  have hmap : Measure.map (fun g : ι → ℝ => g i) (gaussianCouplings ι) =
      gaussianReal 0 1 :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq
  have h := centeredGaussianSquare_memLp_four
  rw [← hmap] at h
  simpa only [Function.comp_def] using h.comp_of_map
    ((by fun_prop : Measurable (fun g : ι → ℝ => g i)).aemeasurable)

private theorem centeredSquareSum_memLp_four (s : Finset ι) :
    MemLp (centeredSquareSum s) 4 (gaussianCouplings ι) := by
  classical
  apply memLp_finsetSum s
  intro i _
  exact centeredSquareCoordinate_memLp_four i

private theorem centeredSquareCoordinate_mean (i : ι) :
    (∫ g : ι → ℝ, centeredGaussianSquare (g i) ∂gaussianCouplings ι) = 0 := by
  have h := integral_comp_eval
    (μ := fun _ : ι => gaussianReal 0 1) (i := i)
    (f := centeredGaussianSquare) (by fun_prop)
  simpa [gaussianCouplings, centeredGaussianSquare_mean] using h

private theorem centeredSquareCoordinate_second (i : ι) :
    (∫ g : ι → ℝ, centeredGaussianSquare (g i) ^ 2
      ∂gaussianCouplings ι) = 1 := by
  have h := integral_comp_eval
    (μ := fun _ : ι => gaussianReal 0 1) (i := i)
    (f := fun x => centeredGaussianSquare x ^ 2) (by fun_prop)
  simpa [gaussianCouplings, centeredGaussianSquare_second_moment] using h

private theorem centeredSquareCoordinate_fourth (i : ι) :
    (∫ g : ι → ℝ, centeredGaussianSquare (g i) ^ 4
      ∂gaussianCouplings ι) = 15 := by
  have h := integral_comp_eval
    (μ := fun _ : ι => gaussianReal 0 1) (i := i)
    (f := fun x => centeredGaussianSquare x ^ 4) (by fun_prop)
  simpa [gaussianCouplings, centeredGaussianSquare_fourth_moment] using h

private theorem centeredSquareSum_mean (s : Finset ι) :
    (∫ g, centeredSquareSum s g ∂gaussianCouplings ι) = 0 := by
  classical
  have hi : ∀ i ∈ s, Integrable
      (fun g : ι → ℝ => centeredGaussianSquare (g i)) (gaussianCouplings ι) := by
    intro i _
    simpa using integrable_pow_le_four (centeredSquareCoordinate_memLp_four i)
      1 (by decide)
  have h := integral_finsetSum (s := s)
    (f := fun i (g : ι → ℝ) => centeredGaussianSquare (g i)) hi
  simp_rw [centeredSquareCoordinate_mean] at h
  simpa [centeredSquareSum] using h

private theorem centeredSquareSum_indep (s : Finset ι) {i : ι} (hi : i ∉ s) :
    IndepFun (centeredSquareSum s)
      (fun g : ι → ℝ => centeredGaussianSquare (g i))
      (gaussianCouplings ι) := by
  let X : ι → (ι → ℝ) → ℝ := fun j g => centeredGaussianSquare (g j)
  have hindep : iIndepFun X (gaussianCouplings ι) := by
    change iIndepFun X (Measure.pi fun _ : ι => gaussianReal 0 1)
    exact iIndepFun_pi (fun _ => (by fun_prop : Measurable centeredGaussianSquare).aemeasurable)
  have hmeas (j : ι) : Measurable (X j) := by
    dsimp [X]
    fun_prop
  have h := hindep.indepFun_finsetSum_of_notMem hmeas hi
  have heq : (∑ j ∈ s, X j) = centeredSquareSum s := by
    funext g
    simp [X, centeredSquareSum, Finset.sum_apply]
  rw [heq] at h
  exact h

private theorem centeredSquareSum_second (s : Finset ι) :
    (∫ g, centeredSquareSum s g ^ 2 ∂gaussianCouplings ι) =
      (s.card : ℝ) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [centeredSquareSum]
  | @insert i s hi ih =>
      have hadd := second_moment_add_of_indep
        (centeredSquareSum_memLp_four s)
        (centeredSquareCoordinate_memLp_four i)
        (centeredSquareSum_indep s hi)
        (centeredSquareSum_mean s)
        (centeredSquareCoordinate_mean i)
      calc
        (∫ g, centeredSquareSum (insert i s) g ^ 2
          ∂gaussianCouplings ι) =
            ∫ g, (centeredSquareSum s g + centeredGaussianSquare (g i)) ^ 2
              ∂gaussianCouplings ι := by
                congr 1
                funext g
                simp [centeredSquareSum, Finset.sum_insert hi, add_comm]
        _ = (s.card : ℝ) + 1 := by
          rw [hadd, ih, centeredSquareCoordinate_second]
        _ = ((insert i s).card : ℝ) := by
          simp [Finset.card_insert_of_notMem hi]

private theorem centeredSquareSum_fourth (s : Finset ι) :
    (∫ g, centeredSquareSum s g ^ 4 ∂gaussianCouplings ι) =
      3 * (s.card : ℝ) ^ 2 + 12 * (s.card : ℝ) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [centeredSquareSum]
  | @insert i s hi ih =>
      have hadd := fourth_moment_add_of_indep
        (centeredSquareSum_memLp_four s)
        (centeredSquareCoordinate_memLp_four i)
        (centeredSquareSum_indep s hi)
        (centeredSquareSum_mean s)
        (centeredSquareCoordinate_mean i)
      calc
        (∫ g, centeredSquareSum (insert i s) g ^ 4
          ∂gaussianCouplings ι) =
            ∫ g, (centeredSquareSum s g + centeredGaussianSquare (g i)) ^ 4
              ∂gaussianCouplings ι := by
                congr 1
                funext g
                simp [centeredSquareSum, Finset.sum_insert hi, add_comm]
        _ = 3 * (s.card : ℝ) ^ 2 + 12 * (s.card : ℝ) +
            6 * (s.card : ℝ) + 15 := by
          rw [hadd, ih, centeredSquareSum_second,
            centeredSquareCoordinate_second, centeredSquareCoordinate_fourth]
          ring
        _ = 3 * ((insert i s).card : ℝ) ^ 2 +
            12 * ((insert i s).card : ℝ) := by
          rw [Finset.card_insert_of_notMem hi]
          push_cast
          ring

/-- Exact fourth moment of the unnormalized independent Gaussian-square sum. -/
theorem centeredGaussianSquares_sum_fourth_moment :
    (∫ g : ι → ℝ,
      (∑ i : ι, centeredGaussianSquare (g i)) ^ 4
      ∂gaussianCouplings ι) =
      3 * (Fintype.card ι : ℝ) ^ 2 + 12 * (Fintype.card ι : ℝ) := by
  simpa [centeredSquareSum] using
    centeredSquareSum_fourth (ι := ι) (Finset.univ : Finset ι)

/-- The normalized quadratic Gaussian sum has a uniformly bounded fourth moment. -/
theorem normalizedGaussianSquares_fourth_moment
    (hcard : 0 < Fintype.card ι) :
    (∫ g : ι → ℝ,
      ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ *
        ∑ i : ι, centeredGaussianSquare (g i)) ^ 4
      ∂gaussianCouplings ι) =
      3 + 12 / (Fintype.card ι : ℝ) := by
  have hM : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
  have hMne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hM
  have hsqrt : Real.sqrt (Fintype.card ι : ℝ) ^ 4 =
      (Fintype.card ι : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt hM.le]
  calc
    (∫ g : ι → ℝ,
      ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ *
        ∑ i : ι, centeredGaussianSquare (g i)) ^ 4
      ∂gaussianCouplings ι) =
        ((Real.sqrt (Fintype.card ι : ℝ))⁻¹) ^ 4 *
          (3 * (Fintype.card ι : ℝ) ^ 2 +
            12 * (Fintype.card ι : ℝ)) := by
          simp only [mul_pow, integral_const_mul,
            centeredGaussianSquares_sum_fourth_moment]
    _ = 3 + 12 / (Fintype.card ι : ℝ) := by
      rw [inv_pow, hsqrt]
      field_simp

theorem normalizedGaussianSquares_fourth_moment_le
    (hcard : 0 < Fintype.card ι) :
    (∫ g : ι → ℝ,
      ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ *
        ∑ i : ι, centeredGaussianSquare (g i)) ^ 4
      ∂gaussianCouplings ι) ≤ 15 := by
  rw [normalizedGaussianSquares_fourth_moment hcard]
  have hM : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
  have hMone : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  have hdiv : 12 / (Fintype.card ι : ℝ) ≤ 12 :=
    (div_le_iff₀ hM).2 (by nlinarith)
  linarith

end GaussianSums

/-- The same fourth-moment bound on the manuscript's Euclidean coupling space. -/
theorem normalizedQuadraticSum_fourth_moment_le (N q : ℕ)
    (hcard : 0 < Fintype.card (InteractionIndex N q)) :
    (∫ g, normalizedQuadraticSum N q g ^ 4
      ∂standardGaussianMeasure N q) ≤ 15 := by
  have hm : Measurable (normalizedQuadraticSum N q) := by
    unfold normalizedQuadraticSum centeredGaussianSquare
    fun_prop
  have hraw : Measurable (fun g : InteractionIndex N q → ℝ =>
      (Real.sqrt (Fintype.card (InteractionIndex N q) : ℝ))⁻¹ *
        ∑ i : InteractionIndex N q, centeredGaussianSquare (g i)) := by
    unfold centeredGaussianSquare
    fun_prop
  calc
    (∫ g, normalizedQuadraticSum N q g ^ 4
      ∂standardGaussianMeasure N q) =
        ∫ x : ℝ, x ^ 4 ∂(standardGaussianMeasure N q).map
          (normalizedQuadraticSum N q) := by
            symm
            exact integral_map hm.aemeasurable (by fun_prop)
    _ = ∫ x : ℝ, x ^ 4 ∂(gaussianCouplings (InteractionIndex N q)).map
          (fun g => (Real.sqrt (Fintype.card (InteractionIndex N q) : ℝ))⁻¹ *
            ∑ i : InteractionIndex N q, centeredGaussianSquare (g i)) := by
            rw [normalizedQuadraticSum_law]
    _ ≤ 15 := by
      rw [integral_map hraw.aemeasurable (by fun_prop)]
      exact normalizedGaussianSquares_fourth_moment_le hcard

theorem Setting.normalizedQuadraticSum_fourth_moment_le {q : ℕ}
    (S : Setting q) (n : ℕ) :
    (∫ g, normalizedQuadraticSum (S.N n) q g ^ 4
      ∂standardGaussianMeasure (S.N n) q) ≤ 15 := by
  apply SYK.CLT.normalizedQuadraticSum_fourth_moment_le
  simpa [InteractionIndex] using Nat.choose_pos (S.q_le_N n)

end SYK.CLT
