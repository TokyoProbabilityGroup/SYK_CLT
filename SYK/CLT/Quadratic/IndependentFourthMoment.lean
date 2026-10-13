import SYK.CLT.Quadratic.GaussianFourthMoment
import SYK.Probability.IndependentMoments

/-!
# Fourth moments of independent finite sums

For independent summands the fourth moment of the unnormalized sum of `n` centered squares is
`3 n² + 12 n` (`centeredGaussianSquares_sum_fourth_moment`), so the normalized sum has fourth
moment `3 + 12/n` (`normalizedGaussianSquares_fourth_moment`) and the uniform bound `15`
(`normalizedGaussianSquares_fourth_moment_le`).
This path does not import the quadratic CLT.
-/

open MeasureTheory ProbabilityTheory

open SYK.GaussianChaos

namespace SYK.CLT

section GaussianSums

variable {ι : Type*} [Fintype ι]

private noncomputable def centeredSquareSum (s : Finset ι) (g : ι → ℝ) : ℝ :=
  ∑ i ∈ s, centeredGaussianSquare (g i)

private theorem centeredSquareSum_memLp_four (s : Finset ι) :
    MemLp (centeredSquareSum s) 4 (gaussianCouplings ι) := by
  classical
  apply memLp_finsetSum s
  intro i _
  exact centeredGaussianSquare_eval_memLp_four i

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
    exact (centeredGaussianSquare_eval_memLp_four i).integrable (by norm_num)
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
    exact iIndepFun_pi (fun _ => centeredGaussianSquare_measurable.aemeasurable)
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
      have hadd := SYK.Probability.second_moment_add_of_indep
        (centeredSquareSum_memLp_four s)
        (centeredGaussianSquare_eval_memLp_four i)
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
      have hadd := SYK.Probability.fourth_moment_add_of_indep
        (centeredSquareSum_memLp_four s)
        (centeredGaussianSquare_eval_memLp_four i)
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

end SYK.CLT
