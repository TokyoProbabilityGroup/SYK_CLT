import Mathlib

set_option autoImplicit false

/-!
# Annealed SYK: final thermodynamic assembly

This file formalizes the dependency-free last layer of the blueprint.  The
paper-specific moment expansion, hypergraph estimates, CCG identity, saddle
point theorem, and concrete Majorana representation are deliberately explicit
hypotheses of the assembly theorems until their modules exist.  Thus every
declaration below is proved, and no missing research theorem is represented by
an unproved declaration.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace SYK
namespace AnnealedFE

/-- Fixed interaction-order assumptions used throughout the high-temperature theorem. -/
structure HTParams where
  q : ℕ
  q_even : Even q
  q_ge_two : 2 ≤ q

/-- The cofinal sequence of physical (even) system sizes starting at `q`. -/
def admissibleSize (q k : ℕ) : ℕ := q + 2 * k

@[simp]
theorem admissibleSize_zero (q : ℕ) : admissibleSize q 0 = q := by
  simp [admissibleSize]

theorem q_le_admissibleSize (q k : ℕ) : q ≤ admissibleSize q k := by
  simp [admissibleSize]

theorem admissibleSize_even {q : ℕ} (hq : Even q) (k : ℕ) :
    Even (admissibleSize q k) := by
  exact hq.add (even_two_mul k)

theorem admissibleSize_pos {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    0 < admissibleSize q k := by
  simp only [admissibleSize]
  omega

/-- Physical sizes packaged with both invariants needed by the finite model. -/
def admissibleSizeSubtype (P : HTParams) (k : ℕ) :
    {N : ℕ // Even N ∧ P.q ≤ N} :=
  ⟨admissibleSize P.q k, admissibleSize_even P.q_even k,
    q_le_admissibleSize P.q k⟩

theorem tendsto_admissibleSize_atTop (q : ℕ) :
    Tendsto (admissibleSize q) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  simp only [admissibleSize]
  omega

/-- A family of finite-volume annealed partition functions.

The concrete Rademacher/Majorana construction from the blueprint will provide
the eventual canonical value of this type.
-/
abbrev PartitionFamily := ℕ → ℕ → ℝ → ℝ

/-- Annealed pressure per Majorana label.  This is well-defined at `β = 0`. -/
def annealedPressure (Z : PartitionFamily) (N q : ℕ) (β : ℝ) : ℝ :=
  Real.log (Z N q β) / (N : ℝ)

/-- The paper's finite-volume annealed free energy (not divided by system size). -/
def annealedFreeEnergy (Z : PartitionFamily) (N q : ℕ) (β : ℝ) : ℝ :=
  Real.log (Z N q β) / β

theorem annealedFreeEnergy_div_size
    (Z : PartitionFamily) (N q : ℕ) (β : ℝ) :
    annealedFreeEnergy Z N q β / (N : ℝ) =
      annealedPressure Z N q β / β := by
  simp only [annealedFreeEnergy, annealedPressure]
  ring

@[simp]
theorem annealedPressure_zero
    (Z : PartitionFamily) (N q : ℕ) (hZ : Z N q 0 = 1) :
    annealedPressure Z N q 0 = 0 := by
  simp [annealedPressure, hZ]

theorem annealed_pressure_limit_zero
    (Z : PartitionFamily) (q : ℕ)
    (hZ : ∀ k, Z (admissibleSize q k) q 0 = 1) :
    Tendsto
      (fun k => annealedPressure Z (admissibleSize q k) q 0)
      atTop (𝓝 0) := by
  simpa only [annealedPressure, hZ, Real.log_one, zero_div] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Total extension of a formula which contains `ρ⁻¹` away from `β = 0`. -/
def extendAtBetaZeroC (paperFormula : ℝ → ℂ → ℂ) (β : ℝ) (z : ℂ) : ℂ :=
  if β = 0 then z else paperFormula β z

@[simp]
theorem extendAtBetaZeroC_zero (paperFormula : ℝ → ℂ → ℂ) (z : ℂ) :
    extendAtBetaZeroC paperFormula 0 z = z := by
  simp [extendAtBetaZeroC]

theorem extendAtBetaZeroC_eq_paper
    (paperFormula : ℝ → ℂ → ℂ) {β : ℝ} (hβ : β ≠ 0) (z : ℂ) :
    extendAtBetaZeroC paperFormula β z = paperFormula β z := by
  simp [extendAtBetaZeroC, hβ]

/-- Restriction of a complex analytic series to its real part on the real axis. -/
def realRestriction (F : ℂ → ℂ) (t : ℝ) : ℝ :=
  (F (t : ℂ)).re

@[simp]
theorem realRestriction_id (t : ℝ) :
    realRestriction id t = t := by
  simp [realRestriction]

/-- The exponent selected by the saddle point, before division by `β`. -/
def saddlePressureValue (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Φ t - 1 - Real.log t

/-- The stationary equation used in the coefficient theorem. -/
def IsStationaryPoint (Φ : ℂ → ℂ) (t : ℝ) : Prop :=
  (t : ℂ) * deriv Φ (t : ℂ) = 1

theorem stationaryPoint_pos {t : ℝ}
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)) : 0 < t := by
  linarith [ht.1]

theorem stationaryPoint_ne_zero {t : ℝ}
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)) : t ≠ 0 :=
  (stationaryPoint_pos ht).ne'

/-- Rewrite the upstream tree-series pressure limit using the CCG identity. -/
theorem annealed_pressure_limit_of_phi_eq_closedFormula
    (Z : PartitionFamily)
    (phiR closedFormulaR : ℕ → ℝ → ℝ → ℝ)
    (tStar : ℕ → ℝ → ℝ)
    (q : ℕ) (β : ℝ)
    (hPressure :
      Tendsto
        (fun k => annealedPressure Z (admissibleSize q k) q β)
        atTop
        (𝓝 (saddlePressureValue (phiR q β) (tStar q β))))
    (hFormula : phiR q β (tStar q β) =
      closedFormulaR q β (tStar q β)) :
    Tendsto
      (fun k => annealedPressure Z (admissibleSize q k) q β)
      atTop
      (𝓝 (saddlePressureValue (closedFormulaR q β) (tStar q β))) := by
  simpa only [saddlePressureValue, hFormula] using hPressure

/-- Divide a proved pressure limit by a fixed nonzero inverse temperature. -/
theorem annealed_freeEnergy_density_limit_of_pressure
    (Z : PartitionFamily) (q : ℕ) (β L : ℝ) (_hβ : β ≠ 0)
    (hPressure :
      Tendsto
        (fun k => annealedPressure Z (admissibleSize q k) q β)
        atTop (𝓝 L)) :
    Tendsto
      (fun k => annealedFreeEnergy Z (admissibleSize q k) q β /
        (admissibleSize q k : ℝ))
      atTop (𝓝 (L / β)) := by
  have h := hPressure.div_const β
  simpa only [annealedFreeEnergy_div_size] using h

/-- Final assembly theorem, conditional only on the two named upstream results. -/
theorem annealed_freeEnergy_density_limit_of_phi_eq_closedFormula
    (Z : PartitionFamily)
    (phiR closedFormulaR : ℕ → ℝ → ℝ → ℝ)
    (tStar : ℕ → ℝ → ℝ)
    (q : ℕ) (β : ℝ) (hβ : β ≠ 0)
    (hPressure :
      Tendsto
        (fun k => annealedPressure Z (admissibleSize q k) q β)
        atTop
        (𝓝 (saddlePressureValue (phiR q β) (tStar q β))))
    (hFormula : phiR q β (tStar q β) =
      closedFormulaR q β (tStar q β)) :
    Tendsto
      (fun k => annealedFreeEnergy Z (admissibleSize q k) q β /
        (admissibleSize q k : ℝ))
      atTop
      (𝓝 (saddlePressureValue (closedFormulaR q β) (tStar q β) / β)) := by
  apply annealed_freeEnergy_density_limit_of_pressure Z q β _ hβ
  exact annealed_pressure_limit_of_phi_eq_closedFormula
    Z phiR closedFormulaR tStar q β hPressure hFormula

theorem annealed_freeEnergy_density_limit_of_pos
    (Z : PartitionFamily) (q : ℕ) {β L : ℝ} (hβ : 0 < β)
    (hPressure :
      Tendsto
        (fun k => annealedPressure Z (admissibleSize q k) q β)
        atTop (𝓝 L)) :
    Tendsto
      (fun k => annealedFreeEnergy Z (admissibleSize q k) q β /
        (admissibleSize q k : ℝ))
      atTop (𝓝 (L / β)) :=
  annealed_freeEnergy_density_limit_of_pressure Z q β L hβ.ne' hPressure

/-- The exact algebraic bridge from the labelled coefficient identity to pressure. -/
theorem pressure_eq_factorial_correction_add_coeff
    (N : ℕ) (hN : N ≠ 0) (M Z : ℝ) (hM : 0 < M)
    (hExact : Z = (N.factorial : ℝ) / (N : ℝ) ^ N * M) :
    Real.log Z / (N : ℝ) =
      (Real.log (N.factorial : ℝ) / (N : ℝ) - Real.log (N : ℝ)) +
        Real.log M / (N : ℝ) := by
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hPow : (N : ℝ) ^ N ≠ 0 := pow_ne_zero _ hNc
  have hFac : (N.factorial : ℝ) ≠ 0 := by positivity
  rw [hExact, Real.log_mul (div_ne_zero hFac hPow) hM.ne',
    Real.log_div hFac hPow, Real.log_pow]
  field_simp

/-- The factorial prefactor `N! / N^N` contributes exactly `-1` to pressure. -/
theorem tendsto_log_factorial_div_sub_log :
    Tendsto
      (fun n : ℕ => Real.log (n.factorial : ℝ) / (n : ℝ) -
        Real.log (n : ℝ))
      atTop (𝓝 (-1 : ℝ)) := by
  have hStirling :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
        atTop (𝓝 0) := by
    have hlog : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) :=
      (Real.continuousAt_log (by positivity)).tendsto.comp
        Stirling.tendsto_stirlingSeq_sqrt_pi
    exact hlog.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hLogNat :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa using h
  have hConst :
      Tendsto (fun n : ℕ => Real.log (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hLogTwo :
      Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    have hsum := hConst.add hLogNat
    have heq :
        (fun n : ℕ => Real.log (2 : ℝ) / (n : ℝ) +
          Real.log (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => Real.log (2 * (n : ℝ)) / (n : ℝ)) := by
      filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
      rw [← add_div]
      congr 1
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by exact_mod_cast hn : (n : ℝ) ≠ 0)]
    simpa only [zero_add] using hsum.congr' heq
  have hTotal :=
    (hStirling.add (hLogTwo.const_mul (1 / 2 : ℝ))).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have heq :
      (fun n : ℕ =>
        Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
          (1 / 2 : ℝ) * (Real.log (2 * (n : ℝ)) / (n : ℝ)) - 1) =ᶠ[atTop]
      (fun n : ℕ =>
        Real.log (n.factorial : ℝ) / (n : ℝ) - Real.log (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hNc : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hLogDiv : Real.log ((n : ℝ) / Real.exp 1) =
        Real.log (n : ℝ) - 1 := by
      rw [Real.log_div hNc (Real.exp_ne_zero 1), Real.log_exp]
    have hFormula := Stirling.log_stirlingSeq_formula n
    rw [hLogDiv] at hFormula
    rw [mul_comm (2 : ℝ) (n : ℝ)] at hFormula
    field_simp [hNc]
    linarith
  simpa using hTotal.congr' heq

/-- Assemble pressure from the exact finite-volume coefficient identity and the
saddle-point asymptotic for that coefficient.

This is the rigorous interface between Sections 11 and 12 of the blueprint.
-/
theorem annealed_pressure_limit_of_coefficient_asymptotics
    (Z : PartitionFamily) (Mcoeff : ℕ → ℝ)
    (closedFormulaR : ℕ → ℝ → ℝ → ℝ)
    (tStar : ℕ → ℝ → ℝ)
    (q : ℕ) (hq : 2 ≤ q) (_hqEven : Even q) (β : ℝ)
    (hExact : ∀ k,
      let N := admissibleSize q k
      Z N q β = (N.factorial : ℝ) / (N : ℝ) ^ N * Mcoeff N)
    (hMcoeffPos : ∀ k, 0 < Mcoeff (admissibleSize q k))
    (hCoeff :
      Tendsto
        (fun k =>
          Real.log (Mcoeff (admissibleSize q k)) /
            (admissibleSize q k : ℝ))
        atTop
        (𝓝 (closedFormulaR q β (tStar q β) -
          Real.log (tStar q β)))) :
    Tendsto
      (fun k => annealedPressure Z (admissibleSize q k) q β)
      atTop
      (𝓝 (saddlePressureValue (closedFormulaR q β) (tStar q β))) := by
  have hCorrection :
      Tendsto
        (fun k =>
          Real.log ((admissibleSize q k).factorial : ℝ) /
              (admissibleSize q k : ℝ) -
            Real.log (admissibleSize q k : ℝ))
        atTop (𝓝 (-1 : ℝ)) := by
    simpa only [Function.comp_apply] using
      tendsto_log_factorial_div_sub_log.comp (tendsto_admissibleSize_atTop q)
  have hSum := hCorrection.add hCoeff
  have heq :
      (fun k =>
        (Real.log ((admissibleSize q k).factorial : ℝ) /
            (admissibleSize q k : ℝ) -
          Real.log (admissibleSize q k : ℝ)) +
        Real.log (Mcoeff (admissibleSize q k)) /
          (admissibleSize q k : ℝ)) =ᶠ[atTop]
      (fun k => annealedPressure Z (admissibleSize q k) q β) := by
    apply Filter.Eventually.of_forall
    intro k
    symm
    simpa only [annealedPressure] using
      pressure_eq_factorial_correction_add_coeff
        (admissibleSize q k) (Nat.ne_of_gt (admissibleSize_pos hq k))
        (Mcoeff (admissibleSize q k)) (Z (admissibleSize q k) q β)
        (hMcoeffPos k) (hExact k)
  have hPressure := hSum.congr' heq
  have hValue :
      (-1 : ℝ) +
          (closedFormulaR q β (tStar q β) - Real.log (tStar q β)) =
        saddlePressureValue (closedFormulaR q β) (tStar q β) := by
    simp only [saddlePressureValue]
    ring
  rw [hValue] at hPressure
  exact hPressure

/-- The free-energy formula obtained from coefficient asymptotics. -/
theorem annealed_freeEnergy_density_limit_of_coefficient_asymptotics
    (Z : PartitionFamily) (Mcoeff : ℕ → ℝ)
    (closedFormulaR : ℕ → ℝ → ℝ → ℝ)
    (tStar : ℕ → ℝ → ℝ)
    (q : ℕ) (hq : 2 ≤ q) (hqEven : Even q) (β : ℝ) (hβ : β ≠ 0)
    (hExact : ∀ k,
      let N := admissibleSize q k
      Z N q β = (N.factorial : ℝ) / (N : ℝ) ^ N * Mcoeff N)
    (hMcoeffPos : ∀ k, 0 < Mcoeff (admissibleSize q k))
    (hCoeff :
      Tendsto
        (fun k =>
          Real.log (Mcoeff (admissibleSize q k)) /
            (admissibleSize q k : ℝ))
        atTop
        (𝓝 (closedFormulaR q β (tStar q β) -
          Real.log (tStar q β)))) :
    Tendsto
      (fun k => annealedFreeEnergy Z (admissibleSize q k) q β /
        (admissibleSize q k : ℝ))
      atTop
      (𝓝 (saddlePressureValue (closedFormulaR q β) (tStar q β) / β)) := by
  apply annealed_freeEnergy_density_limit_of_pressure Z q β _ hβ
  exact annealed_pressure_limit_of_coefficient_asymptotics
    Z Mcoeff closedFormulaR tStar q hq hqEven β hExact hMcoeffPos hCoeff

/-- Generic quantifier wrapper matching the statement order of the paper. -/
theorem exists_highTemperature_window
    {P : ℝ → Prop} {βStar : ℝ} (hβStar : 0 < βStar)
    (hP : ∀ β, |β| ≤ βStar → P β) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β, |β| ≤ β₀ → P β :=
  ⟨βStar, hβStar, hP⟩

end AnnealedFE
end SYK
