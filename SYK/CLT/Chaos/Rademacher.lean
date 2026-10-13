import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import SYK.Probability.GaussianChaos.Orthogonality
import SYK.CLT.Chaos.CliffordSignParity

/-!
# Rademacher bounds for higher SYK chaoses

Finite sign averages and the exponential moment estimate associated with
`lem:Rademacher-encoding` in the CLT manuscript.

`radE` is the uniform average over Boolean vectors, `sgnSum` the sum of signs, and `chaos` the
Rademacher chaos of degree `q`, the elementary symmetric polynomial in the signs.
`even_sum_rademacher_moment` is the finite-sum identity `eq:even-sum-Rademacher-moment`.
Newton's identities evaluate the chaos through the sign sum, and together with an exponential
moment bound for independent signs this gives `rademacher_encoding`: for even `q ≥ 4` and
`0 ≤ t ≤ c_q N^{-(q-1)}`, `𝔼 |S_{N,q}|³ exp (t |S_{N,q}|) ≤ C_q N^{3q/2}`.
-/

open Finset Real

open SYK.GaussianChaos

namespace SYK.CLT.Rademacher

/-- The sign attached to a coin flip: `true ↦ 1`, `false ↦ -1`. -/
noncomputable def rad (b : Bool) : ℝ := if b then 1 else -1

/-- Expectation over `N` independent Rademacher signs: the uniform average over
`{true, false}^N` (this is exactly the joint law of `N` independent Rademachers). -/
noncomputable def radE (N : ℕ) (f : (Fin N → Bool) → ℝ) : ℝ :=
  ((2 : ℝ) ^ N)⁻¹ * ∑ ε : Fin N → Bool, f ε

/-- The Rademacher chaos `S_{N,q} = ∑_{|I| = q} ∏_{x ∈ I} ε_x`. -/
noncomputable def chaos (N q : ℕ) (ε : Fin N → Bool) : ℝ :=
  ∑ I ∈ (univ : Finset (Fin N)).powersetCard q, ∏ x ∈ I, rad (ε x)

/-- The sum of the signs `s = ∑ ε_x`. -/
noncomputable def sgnSum (N : ℕ) (ε : Fin N → Bool) : ℝ := ∑ x, rad (ε x)

lemma abs_rad (b : Bool) : |rad b| = 1 := by cases b <;> simp [rad]

lemma rad_pow (b : Bool) (j : ℕ) : rad b ^ j = if Even j then 1 else rad b := by
  have h2 : rad b ^ 2 = 1 := by cases b <;> simp [rad]
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [if_pos ⟨m, rfl⟩, ← two_mul, pow_mul, h2, one_pow]
  · rw [if_neg (Nat.not_even_iff_odd.mpr ⟨m, rfl⟩), pow_succ, pow_mul, h2, one_pow, one_mul]

lemma abs_sgnSum_le (N : ℕ) (ε : Fin N → Bool) : |sgnSum N ε| ≤ N := by
  unfold sgnSum
  calc |∑ x, rad (ε x)| ≤ ∑ x, |rad (ε x)| := abs_sum_le_sum_abs _ _
    _ = N := by simp [abs_rad]

lemma radE_mono (N : ℕ) {f g : (Fin N → Bool) → ℝ} (h : ∀ ε, f ε ≤ g ε) :
    radE N f ≤ radE N g := by
  unfold radE
  gcongr with ε
  exact h ε

lemma radE_const_mul (N : ℕ) (a : ℝ) (f : (Fin N → Bool) → ℝ) :
    radE N (fun ε => a * f ε) = a * radE N f := by
  unfold radE
  rw [← mul_sum]; ring

lemma radE_sum (N : ℕ) {ι : Type*} (s : Finset ι) (f : ι → (Fin N → Bool) → ℝ) :
    radE N (fun ε => ∑ i ∈ s, f i ε) = ∑ i ∈ s, radE N (f i) := by
  unfold radE
  rw [sum_comm, mul_sum]

/-- The finite-subset definition of the Rademacher chaos is the corresponding
sum over the repository's interaction-index type. -/
lemma chaos_eq_sum_interactionIndex (N q : ℕ) (ε : Fin N → Bool) :
    chaos N q ε =
      ∑ I : InteractionIndex N q, ∏ x ∈ I.1, rad (ε x) := by
  classical
  unfold chaos
  simpa only [InteractionIndex] using
    (Finset.sum_subtype ((Finset.univ : Finset (Fin N)).powersetCard q)
      (fun I => by simp) (fun I => ∏ x ∈ I, rad (ε x)))

/-- Regroup an interaction monomial by vertices.  The exponent at a vertex is
the incidence sum in `IsEvenMultiIndex`. -/
lemma interactionMonomial_eq_vertexProduct (N q : ℕ)
    (α : InteractionIndex N q → ℕ) (ε : Fin N → Bool) :
    (∏ I : InteractionIndex N q,
        (∏ x ∈ I.1, rad (ε x)) ^ α I) =
      ∏ x : Fin N, rad (ε x) ^ (∑ I with x ∈ I.1, α I) := by
  classical
  calc
    (∏ I : InteractionIndex N q,
        (∏ x ∈ I.1, rad (ε x)) ^ α I) =
        ∏ I : InteractionIndex N q,
          ∏ x : Fin N, if x ∈ I.1 then rad (ε x) ^ α I else 1 := by
            apply Finset.prod_congr rfl
            intro I _
            rw [← Finset.prod_filter]
            simp_rw [← Finset.prod_pow]
            simp
    _ = ∏ x : Fin N,
          ∏ I : InteractionIndex N q,
            if x ∈ I.1 then rad (ε x) ^ α I else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ x : Fin N, rad (ε x) ^ (∑ I with x ∈ I.1, α I) := by
          apply Finset.prod_congr rfl
          intro x _
          rw [← Finset.prod_filter]
          simp only [← Finset.prod_pow_eq_pow_sum]

/-- Orthogonality of independent Rademacher monomials on the explicit finite
probability space. -/
lemma radE_vertexProduct (N : ℕ) (m : Fin N → ℕ) :
    radE N (fun ε => ∏ x, rad (ε x) ^ m x) =
      if ∀ x, Even (m x) then 1 else 0 := by
  classical
  unfold radE
  rw [← Fintype.prod_sum (fun x b => rad b ^ m x)]
  by_cases h : ∀ x, Even (m x)
  · rw [if_pos h]
    have hs : ∀ x : Fin N, ∑ b : Bool, rad b ^ m x = 2 := by
      intro x
      rw [show ∑ b : Bool, rad b ^ m x = (2 : ℝ) by
        simp [rad_pow, h x]]
    simp_rw [hs]
    simp [Finset.prod_const]
  · rw [if_neg h]
    push Not at h
    obtain ⟨x, hx⟩ := h
    have hodd : Odd (m x) := Nat.not_even_iff_odd.mp hx
    have hz : ∑ b : Bool, rad b ^ m x = 0 := by
      simp [rad, hodd.neg_one_pow]
    rw [Finset.prod_eq_zero (Finset.mem_univ x) hz, mul_zero]

open scoped Classical in
/-- The expectation of an interaction monomial is one exactly for the even
multi-indices selected by the Clifford sign rule, and zero otherwise. -/
lemma radE_interactionMonomial (N q : ℕ)
    (α : InteractionIndex N q → ℕ) :
    radE N (fun ε =>
      ∏ I : InteractionIndex N q,
        (∏ x ∈ I.1, rad (ε x)) ^ α I) =
      if IsEvenMultiIndex α then 1 else 0 := by
  classical
  have hfun : (fun ε : Fin N → Bool => ∏ I : InteractionIndex N q,
      (∏ x ∈ I.1, rad (ε x)) ^ α I) =
      fun ε => ∏ x : Fin N, rad (ε x) ^ (∑ I with x ∈ I.1, α I) := by
    funext ε
    exact interactionMonomial_eq_vertexProduct N q α ε
  rw [hfun]
  have h := radE_vertexProduct N (fun x => ∑ I with x ∈ I.1, α I)
  by_cases he : IsEvenMultiIndex α
  · have he' : ∀ x : Fin N, Even (∑ I with x ∈ I.1, α I) := he
    simpa [he, he'] using h
  · have he' : ¬ ∀ x : Fin N, Even (∑ I with x ∈ I.1, α I) := he
    simpa [he, he'] using h

open scoped Classical in
/-- Multinomial expansion of the `r`-th moment, with the Rademacher
orthogonality rule already applied. -/
theorem radE_chaos_pow_eq_sum_multinomial_even (N q r : ℕ) :
    radE N (fun ε => chaos N q ε ^ r) =
      ∑ α ∈ (multiIndicesOfDegree (ι := InteractionIndex N q) r).filter IsEvenMultiIndex,
        (Nat.multinomial Finset.univ α : ℝ) := by
  classical
  let w : (Fin N → Bool) → InteractionIndex N q → ℝ :=
    fun ε I => ∏ x ∈ I.1, rad (ε x)
  have hindices :
      Finset.piAntidiag (Finset.univ : Finset (InteractionIndex N q)) r =
        multiIndicesOfDegree (ι := InteractionIndex N q) r := by
    ext α
    rw [Finset.mem_piAntidiag, mem_multiIndicesOfDegree]
    constructor
    · intro h
      simpa using h.1
    · intro h
      exact ⟨by simpa using h, by simp⟩
  have hexpand (ε : Fin N → Bool) :
      chaos N q ε ^ r =
        ∑ α ∈ multiIndicesOfDegree (ι := InteractionIndex N q) r,
          (Nat.multinomial Finset.univ α : ℝ) * ∏ I, w ε I ^ α I := by
    rw [chaos_eq_sum_interactionIndex]
    have h := Finset.sum_pow_eq_sum_piAntidiag
      (Finset.univ : Finset (InteractionIndex N q)) (w ε) r
    simpa only [hindices] using h
  rw [show (fun ε => chaos N q ε ^ r) = fun ε =>
      ∑ α ∈ multiIndicesOfDegree (ι := InteractionIndex N q) r,
        (Nat.multinomial Finset.univ α : ℝ) * ∏ I, w ε I ^ α I by
      funext ε
      exact hexpand ε]
  rw [radE_sum]
  simp_rw [radE_const_mul]
  dsimp [w]
  simp_rw [radE_interactionMonomial]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_filter]

open scoped Classical in
/-- `eq:even-sum-Rademacher-moment`: the factorial-weighted sum over even
multi-indices equals the corresponding Rademacher moment divided by `r!`. -/
theorem even_sum_rademacher_moment (N q r : ℕ) :
    (∑ α ∈ (multiIndicesOfDegree (ι := InteractionIndex N q) r).filter IsEvenMultiIndex,
      (∏ I : InteractionIndex N q, ((α I).factorial : ℝ))⁻¹) =
      ((r.factorial : ℝ)⁻¹ * radE N (fun ε => chaos N q ε ^ r)) := by
  classical
  rw [radE_chaos_pow_eq_sum_multinomial_even, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  simp only [Finset.mem_filter, mem_multiIndicesOfDegree] at hα
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (InteractionIndex N q)) α
  rw [hα.1] at hspec
  have hspecR :
      (∏ I : InteractionIndex N q, ((α I).factorial : ℝ)) *
        (Nat.multinomial Finset.univ α : ℝ) = (r.factorial : ℝ) := by
    exact_mod_cast hspec
  have hprod : (∏ I : InteractionIndex N q, ((α I).factorial : ℝ)) ≠ 0 := by
    positivity
  have hr : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

lemma newton (N k : ℕ) (ε : Fin N → Bool) :
    (k : ℝ) * chaos N k ε = (-1) ^ (k + 1) * ∑ a ∈ antidiagonal k with a.1 < k,
      (-1) ^ a.1 * chaos N a.1 ε * ∑ x, rad (ε x) ^ a.2 := by
  have h := congrArg (MvPolynomial.eval (fun x => rad (ε x)))
    (MvPolynomial.mul_esymm_eq_sum (Fin N) ℝ k)
  simpa [chaos, MvPolynomial.esymm, MvPolynomial.psum, map_sum, map_prod] using h

lemma psum_bound (N j : ℕ) (hj : 1 ≤ j) (ε : Fin N → Bool) :
    |∑ x, rad (ε x) ^ j| ≤ (|sgnSum N ε| + √N) ^ j := by
  simp_rw [rad_pow]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN1 : (1 : ℝ) ≤ √N := by
    rw [one_le_sqrt]; exact_mod_cast hN
  have hu : 1 ≤ |sgnSum N ε| + √N := by linarith [abs_nonneg (sgnSum N ε)]
  by_cases he : Even j
  · simp only [he, if_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Nat.abs_cast]
    have hj2 : 2 ≤ j := by obtain ⟨m, rfl⟩ := he; omega
    calc (N : ℝ) = √N ^ 2 := (sq_sqrt (by positivity)).symm
      _ ≤ (|sgnSum N ε| + √N) ^ 2 := by gcongr; linarith [abs_nonneg (sgnSum N ε)]
      _ ≤ _ := pow_le_pow_right₀ hu hj2
  · simp only [he, if_false]
    calc |∑ x, rad (ε x)| = |sgnSum N ε| := rfl
      _ ≤ (|sgnSum N ε| + √N) ^ 1 := by rw [pow_one]; linarith [sqrt_nonneg (N:ℝ)]
      _ ≤ _ := pow_le_pow_right₀ hu hj

lemma chaos_bound (N k : ℕ) (ε : Fin N → Bool) :
    |chaos N k ε| ≤ (k + 1).factorial * (|sgnSum N ε| + √N) ^ k := by
  set u := |sgnSum N ε| + √N with hu
  have hu0 : 0 ≤ u := by positivity
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [chaos]
  have hterm : ∀ a ∈ (antidiagonal k).filter (fun a => a.1 < k),
      |(-1) ^ a.1 * chaos N a.1 ε * ∑ x, rad (ε x) ^ a.2| ≤ k.factorial * u ^ k := by
    intro a ha
    simp only [mem_filter, mem_antidiagonal] at ha
    obtain ⟨hs, hlt⟩ := ha
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have h1 := ih a.1 hlt
    have h2 := psum_bound N a.2 (by omega) ε
    have hf : ((a.1 + 1).factorial : ℝ) ≤ k.factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    calc |chaos N a.1 ε| * |∑ x, rad (ε x) ^ a.2|
        ≤ ((a.1 + 1).factorial * u ^ a.1) * u ^ a.2 := by
          gcongr
      _ ≤ (k.factorial * u ^ a.1) * u ^ a.2 := by gcongr
      _ = k.factorial * u ^ k := by rw [mul_assoc, ← pow_add, hs]
  have hsum := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
  rw [sum_const] at hsum
  have hcard : ((antidiagonal k).filter (fun a => a.1 < k)).card ≤ k + 1 :=
    (card_filter_le _ _).trans (by simp)
  have hN := congrArg abs (newton N k ε)
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast] at hN
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 ≤ (k.factorial : ℝ) * u ^ k := by positivity
  have : (k : ℝ) * |chaos N k ε| ≤ (k + 1 : ℝ) * (k.factorial * u ^ k) := by
    rw [hN]
    refine hsum.trans ?_
    rw [nsmul_eq_mul]
    gcongr
    exact_mod_cast hcard
  have hfac : ((k + 1).factorial : ℝ) = (k + 1) * k.factorial := by
    push_cast [Nat.factorial_succ]; ring
  rw [hfac]
  nlinarith [abs_nonneg (chaos N k ε)]

lemma radE_exp (N : ℕ) (θ : ℝ) :
    radE N (fun ε => exp (θ * sgnSum N ε)) = cosh θ ^ N := by
  unfold radE sgnSum
  have : ∀ ε : Fin N → Bool, exp (θ * ∑ x, rad (ε x)) = ∏ x, exp (θ * rad (ε x)) := by
    intro ε; rw [mul_sum, exp_sum]
  simp_rw [this]
  rw [← Fintype.prod_sum (fun (_ : Fin N) b => exp (θ * rad b))]
  simp only [Fintype.univ_bool, rad, mul_ite, mul_one, mul_neg, mem_singleton, Bool.true_eq_false,
    not_false_eq_true, sum_insert, ↓reduceIte, sum_singleton, Bool.false_eq_true, prod_const,
    card_univ, Fintype.card_fin, cosh_eq]
  rw [← inv_pow, ← mul_pow]
  congr 1
  ring

lemma radE_cosh_le (N : ℕ) (θ : ℝ) :
    radE N (fun ε => cosh (θ * sgnSum N ε)) ≤ exp (θ ^ 2 / 2) ^ N := by
  have h : radE N (fun ε => cosh (θ * sgnSum N ε)) =
      (radE N (fun ε => exp (θ * sgnSum N ε)) +
        radE N (fun ε => exp ((-θ) * sgnSum N ε))) / 2 := by
    unfold radE
    simp only [cosh_eq, ← sum_div, sum_add_distrib, neg_mul]
    ring
  rw [h, radE_exp, radE_exp, cosh_neg]
  have := cosh_le_exp_half_sq θ
  have h0 : 0 ≤ cosh θ := (cosh_pos θ).le
  have := pow_le_pow_left₀ h0 this N
  linarith

lemma exp_sq_le_sum (M : ℕ) (b : ℝ) (hb : |b| ≤ M) :
    exp (b ^ 2 / 4) ≤ 2 * exp 1 *
      ∑ n ∈ range (M + 2), exp (-(n : ℝ) ^ 2) * cosh (n * b) := by
  set j : ℤ := ⌊b / 2⌋ with hj
  have h1 : (j : ℝ) ≤ b / 2 := Int.floor_le _
  have h1' : b / 2 < j + 1 := Int.lt_floor_add_one _
  have hn : ((j.natAbs : ℕ) : ℝ) = |(j : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h2 : b ^ 2 / 4 ≤ 1 + (-(j : ℝ) ^ 2 + b * j) := by nlinarith
  have h3 : exp (b * j) ≤ 2 * cosh ((j.natAbs : ℕ) * b) := by
    have e : cosh (|(j:ℝ)| * b) = cosh (b * j) := by
      rw [← cosh_abs, abs_mul, abs_abs, ← abs_mul, cosh_abs, mul_comm]
    rw [hn, e, cosh_eq]
    have := exp_pos (-(b * j)); linarith
  have h4 : j.natAbs ∈ range (M + 2) := by
    rw [mem_range]
    have hb' := abs_le.mp hb
    have : |(j : ℝ)| < M + 2 := by
      rw [abs_lt]; constructor <;> linarith
    rw [← hn] at this
    exact_mod_cast this
  have h5 := single_le_sum (f := fun n : ℕ => exp (-(n : ℝ) ^ 2) * cosh (n * b))
    (fun n _ => mul_nonneg (exp_pos _).le (cosh_pos _).le) h4
  have hsq : ((j.natAbs : ℕ) : ℝ) ^ 2 = (j : ℝ) ^ 2 := by rw [hn, sq_abs]
  rw [hsq] at h5
  calc exp (b ^ 2 / 4) ≤ exp (1 + (-(j : ℝ) ^ 2 + b * j)) := exp_le_exp.mpr h2
    _ = exp 1 * exp (-(j : ℝ) ^ 2) * exp (b * j) := by rw [exp_add, exp_add]; ring
    _ ≤ exp 1 * exp (-(j : ℝ) ^ 2) * (2 * cosh ((j.natAbs : ℕ) * b)) := by gcongr
    _ = 2 * exp 1 * (exp (-(j : ℝ) ^ 2) * cosh ((j.natAbs : ℕ) * b)) := by ring
    _ ≤ _ := by gcongr

lemma subgaussian (N : ℕ) (hN : 1 ≤ N) :
    radE N (fun ε => exp (sgnSum N ε ^ 2 / (4 * N))) ≤
      2 * exp 1 / (1 - exp (-1 / 2)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : (0 : ℝ) < √N := sqrt_pos.mpr hN'
  have hsN : √(N : ℝ) ≤ N := by
    rw [sqrt_le_left hN'.le]; nlinarith [(by exact_mod_cast hN : (1 : ℝ) ≤ N)]
  have hpt : ∀ ε : Fin N → Bool, exp (sgnSum N ε ^ 2 / (4 * N)) ≤ 2 * exp 1 *
      ∑ n ∈ range (N + 2), exp (-(n : ℝ) ^ 2) * cosh ((n / √N) * sgnSum N ε) := by
    intro ε
    have hb : |sgnSum N ε / √N| ≤ N := by
      rw [abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
      have := abs_sgnSum_le N ε
      have : (N : ℝ) = √N * √N := (mul_self_sqrt hN'.le).symm
      nlinarith
    have := exp_sq_le_sum N _ hb
    have e1 : (sgnSum N ε / √N) ^ 2 / 4 = sgnSum N ε ^ 2 / (4 * N) := by
      rw [div_pow, sq_sqrt hN'.le]; ring
    have e2 : ∀ n : ℕ, (n : ℝ) * (sgnSum N ε / √N) = (n / √N) * sgnSum N ε := by
      intro n; ring
    simpa only [e1, e2] using this
  refine (radE_mono N hpt).trans ?_
  rw [radE_const_mul, radE_sum]
  have hr0 : 0 ≤ exp (-1 / 2) := (exp_pos _).le
  have hr1 : exp (-1 / 2) < 1 := exp_lt_one_iff.mpr (by norm_num)
  have key : ∀ n ∈ range (N + 2), radE N (fun ε => exp (-(n : ℝ) ^ 2) *
      cosh ((n / √N) * sgnSum N ε)) ≤ exp (-1 / 2) ^ n := by
    intro n _
    rw [radE_const_mul]
    refine (mul_le_mul_of_nonneg_left (radE_cosh_le N _) (exp_pos _).le).trans ?_
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
    apply exp_le_exp.mpr
    rw [div_pow, sq_sqrt hN'.le]
    field_simp
    have : (n : ℝ) ≤ n ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := N + 2) hr0 hr1
  simp only [Nat.Ico_zero_eq_range, pow_zero] at hg
  have := (sum_le_sum key).trans hg
  have he : 0 < 2 * exp 1 := by positivity
  calc 2 * exp 1 * ∑ n ∈ range (N + 2), radE N (fun ε => exp (-(n : ℝ) ^ 2) *
      cosh ((n / √N) * sgnSum N ε)) ≤ 2 * exp 1 * (1 / (1 - exp (-1 / 2))) := by gcongr
    _ = _ := by ring

lemma pointwise_bound (k N : ℕ) (hN : 1 ≤ N) (c t : ℝ)
    (hc : c * (2 * k + 1).factorial = 1 / 2 ^ (2 * k + 2))
    (ht0 : 0 ≤ t) (ht : t ≤ c / (N : ℝ) ^ (2 * k - 1)) (hk : 1 ≤ k) (ε : Fin N → Bool) :
    |chaos N (2 * k) ε| ^ 3 * exp (t * |chaos N (2 * k) ε|) ≤
      ((2 * k + 1).factorial ^ 3 * 16 ^ (3 * k) * (3 * k).factorial * exp (1 / 4)) *
        (N : ℝ) ^ (3 * k) * exp (sgnSum N ε ^ 2 / (4 * N)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [e1] at ht
  set B : ℝ := ((2 * (m + 1) + 1).factorial : ℝ) with hB
  set S := chaos N (2 * (m + 1)) ε
  set s := sgnSum N ε
  set u := |s| + √N with hu
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set x := s ^ 2 / N with hx
  have hx0 : 0 ≤ x := by positivity
  have hB0 : 0 < B := by positivity
  have hu0 : 0 ≤ u := by positivity
  have hS : |S| ≤ B * u ^ (2 * (m + 1)) := chaos_bound N _ ε
  have hsq : √(N : ℝ) ^ 2 = N := sq_sqrt hN'.le
  have hu2 : u ^ 2 ≤ 2 * N * (1 + x) := by
    have : 2 * N * (1 + x) = 2 * N + 2 * s ^ 2 := by
      rw [hx]; field_simp
    rw [this, hu]
    nlinarith [sq_abs s, sq_nonneg (|s| - √N)]
  have hule : u ≤ 2 * N := by
    have h1 := abs_sgnSum_le N ε
    have h2 : √(N : ℝ) ≤ N := by
      rw [sqrt_le_left hN'.le]; nlinarith
    rw [hu]; linarith
  have hpow : u ^ (2 * (m + 1)) ≤ (1 + x) * 2 ^ (2 * m + 1) * (N : ℝ) ^ (2 * m + 1) := by
    have e : u ^ (2 * (m + 1)) = u ^ 2 * u ^ (2 * m) := by rw [← pow_add]; ring_nf
    rw [e]
    calc u ^ 2 * u ^ (2 * m) ≤ (2 * N * (1 + x)) * (2 * N) ^ (2 * m) := by
          gcongr
      _ = _ := by rw [mul_pow, pow_succ, pow_succ]; ring
  have htS : t * |S| ≤ (1 + x) / 8 := by
    have hNp : (0 : ℝ) < (N : ℝ) ^ (2 * m + 1) := by positivity
    calc t * |S| ≤ (c / (N : ℝ) ^ (2 * m + 1)) * (B * u ^ (2 * (m + 1))) := by
          gcongr
          exact ht0.trans ht
      _ = (c * B) * u ^ (2 * (m + 1)) / (N : ℝ) ^ (2 * m + 1) := by ring
      _ ≤ (c * B) * ((1 + x) * 2 ^ (2 * m + 1) * (N : ℝ) ^ (2 * m + 1)) /
            (N : ℝ) ^ (2 * m + 1) := by
          gcongr
          rw [hB, hc]; positivity
      _ = (1 + x) / 8 := by
          rw [hB, hc]; field_simp; ring
  have h3 : |S| ^ 3 ≤ B ^ 3 * (2 * N * (1 + x)) ^ (3 * (m + 1)) := by
    calc |S| ^ 3 ≤ (B * u ^ (2 * (m + 1))) ^ 3 := by gcongr
      _ = B ^ 3 * (u ^ 2) ^ (3 * (m + 1)) := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
      _ ≤ _ := by gcongr
  have h4 : (1 + x) ^ (3 * (m + 1)) ≤
      8 ^ (3 * (m + 1)) * (3 * (m + 1)).factorial * exp ((1 + x) / 8) := by
    have := pow_div_factorial_le_exp (x := (1 + x) / 8) (by positivity) (3 * (m + 1))
    rw [div_le_iff₀ (by positivity), div_pow] at this
    have h8 : (0 : ℝ) < 8 ^ (3 * (m + 1)) := by positivity
    rw [div_le_iff₀ h8] at this
    linarith
  calc |S| ^ 3 * exp (t * |S|) ≤ (B ^ 3 * (2 * N * (1 + x)) ^ (3 * (m + 1))) *
        exp ((1 + x) / 8) := by gcongr
    _ = B ^ 3 * (2 * N) ^ (3 * (m + 1)) * (1 + x) ^ (3 * (m + 1)) * exp ((1 + x) / 8) := by
        rw [mul_pow]; ring
    _ ≤ B ^ 3 * (2 * N) ^ (3 * (m + 1)) *
        (8 ^ (3 * (m + 1)) * (3 * (m + 1)).factorial * exp ((1 + x) / 8)) *
        exp ((1 + x) / 8) := by gcongr
    _ = (B ^ 3 * 16 ^ (3 * (m + 1)) * (3 * (m + 1)).factorial) * (N : ℝ) ^ (3 * (m + 1)) *
        (exp ((1 + x) / 8) * exp ((1 + x) / 8)) := by
        rw [mul_pow, show (16 : ℝ) = 2 * 8 by norm_num, mul_pow]; ring
    _ = _ := by
        rw [← exp_add]
        have : (1 + x) / 8 + (1 + x) / 8 = 1 / 4 + s ^ 2 / (4 * N) := by
          rw [hx]; field_simp; ring
        rw [this, exp_add]; ring

/-- **Exponential moment bound for the Rademacher chaos.**
For `q ≥ 4` even there are `c_q > 0` and `C_q < ∞` such that
`𝔼_ε[|S_{N,q}|^3 e^{t|S_{N,q}|}] ≤ C_q N^{3q/2}` for every `N` and every
`0 ≤ t ≤ c_q N^{-(q-1)}`.

Here `𝔼_ε` is `radE N`, the uniform average over all `2^N` sign patterns, and
`N^{-(q-1)}`, `N^{3q/2}` are real powers (for `N = 0` both sides vanish).

Proof outline: Newton's identities give `|S_{N,q}| ≤ (q+1)! (|s| + √N)^q` with
`s = ∑ ε_x`; this turns `t|S_{N,q}|` into at most `(1 + s²/N)/8`, and the polynomial
factor into `N^{3q/2}` times `e^{(1+s²/N)/8}`. One concludes with the sub-Gaussian bound
`𝔼 e^{s²/(4N)} ≤ 2e/(1 - e^{-1/2})`. -/
theorem rademacher_encoding (q : ℕ) (hq : 4 ≤ q) (hqe : Even q) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, ∀ t : ℝ, 0 ≤ t →
      t ≤ c * (N : ℝ) ^ (-((q : ℝ) - 1)) →
      radE N (fun ε => |chaos N q ε| ^ 3 * exp (t * |chaos N q ε|)) ≤
        C * (N : ℝ) ^ ((3 * q : ℝ) / 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k := by
    obtain ⟨r, hr⟩ := hqe; exact ⟨r, by omega⟩
  have hk : 1 ≤ k := by omega
  set B : ℝ := ((2 * k + 1).factorial : ℝ) with hB
  have hB0 : 0 < B := by positivity
  set A : ℝ := (2 * k + 1).factorial ^ 3 * 16 ^ (3 * k) * (3 * k).factorial * exp (1 / 4)
  set K : ℝ := 2 * exp 1 / (1 - exp (-1 / 2))
  have hA : 0 ≤ A := by positivity
  refine ⟨1 / 2 ^ (2 * k + 2) / B, by positivity, A * K, ?_⟩
  intro N t ht0 ht
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hz : ∀ ε : Fin 0 → Bool, chaos 0 (2 * k) ε = 0 := by
      intro ε
      rw [chaos, powersetCard_eq_empty.mpr (by simp; omega), sum_empty]
    simp only [hz, abs_zero]
    unfold radE
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [Nat.cast_zero, zero_rpow (by positivity)]
    simp
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : ((2 * k : ℕ) : ℝ) - 1 = ((2 * k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : (3 * ((2 * k : ℕ) : ℝ)) / 2 = ((3 * k : ℕ) : ℝ) := by push_cast; ring
  rw [e1, rpow_neg hN'.le, rpow_natCast, ← div_eq_mul_inv] at ht
  rw [e2, rpow_natCast]
  have hc : 1 / 2 ^ (2 * k + 2) / B * (2 * k + 1).factorial = 1 / 2 ^ (2 * k + 2) := by
    rw [← hB]; field_simp
  have hpt := fun ε => pointwise_bound k N hN _ t hc ht0 ht hk ε
  refine (radE_mono N hpt).trans ?_
  rw [radE_const_mul]
  have := subgaussian N hN
  have hAN : 0 ≤ A * (N : ℝ) ^ (3 * k) := by positivity
  calc A * (N : ℝ) ^ (3 * k) * radE N (fun ε => exp (sgnSum N ε ^ 2 / (4 * N)))
      ≤ A * (N : ℝ) ^ (3 * k) * K := by gcongr
    _ = A * K * (N : ℝ) ^ (3 * k) := by ring

end SYK.CLT.Rademacher
