import SYK.CLT.Lemmas.Preliminaries
import SYK.CLT.Lemmas.PartitionDerivatives

/-!
# Exact second chaos of the SYK partition function

The parity selection rule reduces the degree-two projection in
`prop:exact-second-chaos` to the diagonal Hermite multi-indices. Signed vertex
permutations and first-order Gaussian integration by parts identify the common
coefficient at every real inverse temperature. Main entry point: `Setting.Y_secondChaos_eq`.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace SYK.CLT

/-- The degree-two multi-indices supported at one interaction. -/
noncomputable def diagonalMultiIndices (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Finset (ι → ℕ) :=
  (multiIndices_degree (ι := ι) 2).filter (fun α => ∃ I, α = Pi.single I 2)

theorem diagonalMultiIndices_eq_image (ι : Type*) [Fintype ι] [DecidableEq ι] :
    diagonalMultiIndices ι = (Finset.univ : Finset ι).image (fun I => Pi.single I 2) := by
  classical
  ext α
  constructor
  · intro hα
    obtain ⟨I, rfl⟩ := (Finset.mem_filter.mp hα).2
    simp
  · intro hα
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hα
    apply Finset.mem_filter.mpr
    constructor
    · exact (mem_multiIndices_degree 2 _).mpr (by simp)
    · exact ⟨I, rfl⟩

theorem hermiteFactorial_single_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι) :
    (∏ J : ι, (((Pi.single I 2 : ι → ℕ) J).factorial : ℝ)) = 2 := by
  classical
  rw [Finset.prod_eq_single I]
  · simp
  · intro J _ hJI
    simp [hJI]
  · simp

/-- The diagonal degree-two Hermite product is `g_I² - 1`. -/
theorem hermiteMulti_single_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι) (g : ι → ℝ) :
    SYK.hermiteMulti (Pi.single I 2) g = g I ^ 2 - 1 := by
  classical
  simp only [SYK.hermiteMulti]
  rw [Finset.prod_eq_single I]
  · simp [pow_two]
  · intro J _ hJI
    simp [hJI, Polynomial.hermite_zero]
  · simp

/-- The diagonal Hermite coefficient is the manuscript's Gaussian expectation. -/
theorem Setting.inner_single_two_Y_eq_integral {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) (I : InteractionIndex (S.N n) q) :
    ⟪hermiteLp (Pi.single I 2), S.YGaussianLp β n⟫_ℝ =
      ∫ g : InteractionIndex (S.N n) q → ℝ,
        S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
          ∂gaussianCouplings (InteractionIndex (S.N n) q) := by
  rw [MeasureTheory.L2.inner_def]
  have hH := (hermiteMulti_memLp_two (Pi.single I 2)).coeFn_toLp
  have hY := S.YGaussianLp_ae β n
  apply integral_congr_ae
  filter_upwards [hH, hY] with g hgH hgY
  change (S.YGaussianLp β n) g * (hermiteLp (Pi.single I 2)) g = _
  rw [show (hermiteLp (Pi.single I 2)) g = hermiteMulti (Pi.single I 2) g from hgH,
    hgY, hermiteMulti_single_two]

/-- Parity removes every off-diagonal term from the second chaos of `Y_N`. -/
theorem Setting.Y_secondChaos_eq_diagonal {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    hermiteDegreeProjection 2 (S.YGaussianLp β n) =
      hermiteFiniteProjection (diagonalMultiIndices (InteractionIndex (S.N n) q))
        (S.YGaussianLp β n) := by
  classical
  unfold hermiteDegreeProjection hermiteFiniteProjection diagonalMultiIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α hα
  by_cases hdiag : ∃ I, α = Pi.single I 2
  · simp [hdiag]
  · have hdegree := (mem_multiIndices_degree 2 α).mp hα
    obtain hdiag' | ⟨I, J, hIJ, hpair⟩ := multiIndex_degree_two_cases α hdegree
    · exact absurd hdiag' hdiag
    · subst α
      simp [hdiag, S.inner_offDiagonal_secondChaos_eq_zero β n I J hIJ]

/-- The second chaos is a sum of diagonal Hermite terms, with its finite-size
coefficients displayed individually. -/
theorem Setting.Y_secondChaos_eq_sum_diagonal {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    hermiteDegreeProjection 2 (S.YGaussianLp β n) =
      ∑ I : InteractionIndex (S.N n) q,
        (⟪hermiteLp (Pi.single I 2), S.YGaussianLp β n⟫_ℝ /
          ∏ J : InteractionIndex (S.N n) q,
            (((Pi.single I 2 : InteractionIndex (S.N n) q → ℕ) J).factorial : ℝ)) •
          hermiteLp (Pi.single I 2) := by
  classical
  rw [S.Y_secondChaos_eq_diagonal, diagonalMultiIndices_eq_image]
  unfold hermiteFiniteProjection
  rw [Finset.sum_image]
  intro I _ J _ hIJ
  by_contra hne
  have h := congrFun hIJ I
  simp [hne] at h

/-- Each diagonal Hermite product has squared norm two. -/
theorem Setting.Y_secondChaos_eq_half_sum {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    hermiteDegreeProjection 2 (S.YGaussianLp β n) =
      ∑ I : InteractionIndex (S.N n) q,
        (⟪hermiteLp (Pi.single I 2), S.YGaussianLp β n⟫_ℝ / 2) •
          hermiteLp (Pi.single I 2) := by
  simpa only [hermiteFactorial_single_two] using S.Y_secondChaos_eq_sum_diagonal β n

/-- Exact finite-size second-chaos expansion before identifying the common
coefficient across interactions. -/
theorem Setting.Y_secondChaos_eq_integral_sum {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ) :
    hermiteDegreeProjection 2 (S.YGaussianLp β n) =
      ∑ I : InteractionIndex (S.N n) q,
        ((∫ g : InteractionIndex (S.N n) q → ℝ,
            S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
              ∂gaussianCouplings (InteractionIndex (S.N n) q)) / 2) •
          hermiteLp (Pi.single I 2) := by
  simpa only [S.inner_single_two_Y_eq_integral] using S.Y_secondChaos_eq_half_sum β n

/-- The algebraic conclusion of `prop:exact-second-chaos`. The two inputs are
the interaction-index symmetry of the diagonal coefficient and the radial
derivative identity for its sum. -/
theorem Setting.Y_secondChaos_eq_common_of_symmetry_and_sum {q : ℕ} (S : Setting q)
    (β : ℝ) (n : ℕ)
    (hsym : ∀ I J : InteractionIndex (S.N n) q,
      (∫ g : InteractionIndex (S.N n) q → ℝ,
          S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
            ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
        ∫ g : InteractionIndex (S.N n) q → ℝ,
          S.Y β n (WithLp.toLp 2 g) * (g J ^ 2 - 1)
            ∂gaussianCouplings (InteractionIndex (S.N n) q))
    (hsum : (∑ I : InteractionIndex (S.N n) q,
      ∫ g : InteractionIndex (S.N n) q → ℝ,
        S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
          ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
        β * deriv (fun b => Real.log (S.meanZ b n)) β) :
    hermiteDegreeProjection 2 (S.YGaussianLp β n) =
      (β * deriv (fun b => Real.log (S.meanZ b n)) β /
        (2 * (Nat.choose (S.N n) q : ℝ))) •
        ∑ I : InteractionIndex (S.N n) q, hermiteLp (Pi.single I 2) := by
  classical
  have hcard : (Fintype.card (InteractionIndex (S.N n) q) : ℝ) =
      (Nat.choose (S.N n) q : ℝ) := by simp [InteractionIndex]
  have hcard_ne : (Nat.choose (S.N n) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (S.q_le_N n)).ne'
  have hcoeff (I : InteractionIndex (S.N n) q) :
      (∫ g : InteractionIndex (S.N n) q → ℝ,
        S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
          ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
        β * deriv (fun b => Real.log (S.meanZ b n)) β /
          (Nat.choose (S.N n) q : ℝ) := by
    have hsumI : (∑ J : InteractionIndex (S.N n) q,
        ∫ g : InteractionIndex (S.N n) q → ℝ,
          S.Y β n (WithLp.toLp 2 g) * (g I ^ 2 - 1)
            ∂gaussianCouplings (InteractionIndex (S.N n) q)) =
        β * deriv (fun b => Real.log (S.meanZ b n)) β := by
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro J _
      exact (hsym J I).symm
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hsumI
    apply (eq_div_iff hcard_ne).2
    simpa only [mul_comm (Nat.choose (S.N n) q : ℝ)] using hsumI
  rw [S.Y_secondChaos_eq_integral_sum]
  simp_rw [hcoeff]
  rw [← Finset.smul_sum]
  congr 1
  field_simp

/-- `prop:exact-second-chaos`, with symmetry and derivative exchange proved for
the finite model. The equality is in Gaussian `L²`, for every real `β`. -/
theorem Setting.Y_secondChaos_eq {q : ℕ} (S : Setting q) (β : ℝ) (n : ℕ) :
    hermiteDegreeProjection 2 (S.YGaussianLp β n) =
      (β * deriv (fun b => Real.log (S.meanZ b n)) β /
        (2 * (Nat.choose (S.N n) q : ℝ))) •
        ∑ I : InteractionIndex (S.N n) q, hermiteLp (Pi.single I 2) :=
  S.Y_secondChaos_eq_common_of_symmetry_and_sum β n
    (S.integral_Y_mul_sq_sub_one_eq β n) (S.sum_integral_Y_mul_sq_sub_one β n)

end SYK.CLT
