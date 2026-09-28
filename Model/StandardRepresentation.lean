import SYK.Model.Majorana
import SYK.Model.FiniteDimensionalGibbs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Standard Jordan–Wigner representation

The recursive qubit basis realizes `2*m` Majorana generators in dimension
`2^m`, with the Pauli-Y sign convention of the lecture notes. Interactions use
exactly the shared increasing product and phase, without extra structure fields.
-/

open scoped BigOperators Kronecker

namespace SYK

/-- The computational basis of `m` qubits, with the first site outermost. -/
@[reducible]
def StandardBasis : ℕ → Type
  | 0 => Unit
  | m + 1 => Fin 2 × StandardBasis m

instance standardBasisFintype : (m : ℕ) → Fintype (StandardBasis m)
  | 0 => inferInstanceAs (Fintype Unit)
  | m + 1 => by
      letI := standardBasisFintype m
      exact inferInstanceAs (Fintype (Fin 2 × StandardBasis m))

instance standardBasisDecidableEq : (m : ℕ) → DecidableEq (StandardBasis m)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | m + 1 => by
      letI := standardBasisDecidableEq m
      exact inferInstanceAs (DecidableEq (Fin 2 × StandardBasis m))

instance standardBasisNonempty : (m : ℕ) → Nonempty (StandardBasis m)
  | 0 => inferInstanceAs (Nonempty Unit)
  | m + 1 => by
      letI := standardBasisNonempty m
      exact inferInstanceAs (Nonempty (Fin 2 × StandardBasis m))

/-- The qubit basis has dimension `2^m`. -/
@[simp]
theorem standardBasis_card (m : ℕ) : Fintype.card (StandardBasis m) = 2 ^ m := by
  induction m with
  | zero => simp [StandardBasis]
  | succ m ih => simp [StandardBasis, Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

/-- Pauli X and Y, with Y = [[0,-i],[i,0]]. -/
def jordanWignerPauli (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if b = 0 then !![0, 1; 1, 0] else !![0, -Complex.I; Complex.I, 0]

/-- Pauli Z, the parity string factor. -/
def jordanWignerZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

private theorem pauli_sq (b : Fin 2) : jordanWignerPauli b * jordanWignerPauli b = 1 := by
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [jordanWignerPauli, Matrix.mul_apply, Fin.sum_univ_two]

private theorem z_sq : jordanWignerZ * jordanWignerZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [jordanWignerZ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem pauli_star (b : Fin 2) : star (jordanWignerPauli b) = jordanWignerPauli b := by
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [jordanWignerPauli, Matrix.star_eq_conjTranspose]

private theorem z_star : star jordanWignerZ = jordanWignerZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [jordanWignerZ, Matrix.star_eq_conjTranspose]

private theorem pauli_anticommute (b c : Fin 2) (h : b ≠ c) :
    jordanWignerPauli b * jordanWignerPauli c = -(jordanWignerPauli c * jordanWignerPauli b) := by
  fin_cases b <;> fin_cases c <;> try contradiction
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [jordanWignerPauli, Matrix.mul_apply, Fin.sum_univ_two]

private theorem pauli_z_anticommute (b : Fin 2) :
    jordanWignerPauli b * jordanWignerZ = -(jordanWignerZ * jordanWignerPauli b) := by
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [jordanWignerPauli, jordanWignerZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Jordan–Wigner generator at a site and X/Y label. Recursion adds a leading Z
at every earlier site and identity factors at every later site. -/
def jordanWigner : (m : ℕ) → Fin m → Fin 2 → Matrix (StandardBasis m) (StandardBasis m) ℂ
  | 0, i, _ => Fin.elim0 i
  | m + 1, i, b => Fin.cases
      (jordanWignerPauli b ⊗ₖ (1 : Matrix (StandardBasis m) (StandardBasis m) ℂ))
      (fun j => jordanWignerZ ⊗ₖ jordanWigner m j b) i

/-- Each Jordan–Wigner generator squares to the identity. -/
theorem jordanWigner_sq (m : ℕ) (i : Fin m) (b : Fin 2) :
    jordanWigner m i b * jordanWigner m i b = 1 := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change (jordanWignerPauli b ⊗ₖ (1 : Matrix (StandardBasis m) _ ℂ)) *
          (jordanWignerPauli b ⊗ₖ 1) = 1
        rw [← Matrix.mul_kronecker_mul, pauli_sq, Matrix.one_mul, Matrix.one_kronecker_one]
      · change (jordanWignerZ ⊗ₖ jordanWigner m j b) *
          (jordanWignerZ ⊗ₖ jordanWigner m j b) = 1
        rw [← Matrix.mul_kronecker_mul, z_sq, ih, Matrix.one_kronecker_one]

/-- The generators are self-adjoint with the lecture notes' Pauli-Y convention. -/
theorem jordanWigner_self_adjoint (m : ℕ) (i : Fin m) (b : Fin 2) :
    star (jordanWigner m i b) = jordanWigner m i b := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change star (jordanWignerPauli b ⊗ₖ (1 : Matrix (StandardBasis m) _ ℂ)) =
          jordanWignerPauli b ⊗ₖ 1
        simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
          Matrix.conjTranspose_one]
        rw [← Matrix.star_eq_conjTranspose, pauli_star]
      · change star (jordanWignerZ ⊗ₖ jordanWigner m j b) =
          jordanWignerZ ⊗ₖ jordanWigner m j b
        simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
        rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, z_star, ih]

/-- Distinct site/type pairs anticommute. -/
theorem jordanWigner_anticommute (m : ℕ) (i j : Fin m) (b c : Fin 2)
    (h : i ≠ j ∨ b ≠ c) :
    jordanWigner m i b * jordanWigner m j c =
      -(jordanWigner m j c * jordanWigner m i b) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
      induction i using Fin.cases with
      | zero =>
          induction j using Fin.cases with
          | zero =>
              have hbc : b ≠ c := by simpa using h
              change (jordanWignerPauli b ⊗ₖ (1 : Matrix (StandardBasis m) _ ℂ)) *
                  (jordanWignerPauli c ⊗ₖ 1) = -((jordanWignerPauli c ⊗ₖ 1) *
                  (jordanWignerPauli b ⊗ₖ 1))
              rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
                Matrix.one_mul, pauli_anticommute b c hbc]
              ext u v
              simp
          | succ j =>
              change (jordanWignerPauli b ⊗ₖ (1 : Matrix (StandardBasis m) _ ℂ)) *
                  (jordanWignerZ ⊗ₖ jordanWigner m j c) =
                -((jordanWignerZ ⊗ₖ jordanWigner m j c) * (jordanWignerPauli b ⊗ₖ 1))
              rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
                Matrix.one_mul, Matrix.mul_one, pauli_z_anticommute]
              ext u v
              simp
      | succ i =>
          induction j using Fin.cases with
          | zero =>
              have hz : jordanWignerZ * jordanWignerPauli c =
                  -(jordanWignerPauli c * jordanWignerZ) := by
                simpa only [neg_neg] using congrArg Neg.neg (pauli_z_anticommute c).symm
              change (jordanWignerZ ⊗ₖ jordanWigner m i b) *
                  (jordanWignerPauli c ⊗ₖ (1 : Matrix (StandardBasis m) _ ℂ)) =
                -((jordanWignerPauli c ⊗ₖ 1) * (jordanWignerZ ⊗ₖ jordanWigner m i b))
              rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
                Matrix.one_mul, Matrix.mul_one, hz]
              ext u v
              simp
          | succ j =>
              have hij : i ≠ j ∨ b ≠ c := by simpa using h
              change (jordanWignerZ ⊗ₖ jordanWigner m i b) *
                  (jordanWignerZ ⊗ₖ jordanWigner m j c) =
                -((jordanWignerZ ⊗ₖ jordanWigner m j c) * (jordanWignerZ ⊗ₖ jordanWigner m i b))
              rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, z_sq, ih i j hij]
              ext u v
              simp

/-- The first site acts by Pauli X/Y with identity on the remaining sites. -/
@[simp]
theorem jordanWigner_zero (m : ℕ) (b : Fin 2) :
    jordanWigner (m + 1) 0 b =
      jordanWignerPauli b ⊗ₖ (1 : Matrix (StandardBasis m) (StandardBasis m) ℂ) := rfl

/-- A later site acquires one leading parity-string factor. -/
@[simp]
theorem jordanWigner_succ (m : ℕ) (i : Fin m) (b : Fin 2) :
    jordanWigner (m + 1) i.succ b = jordanWignerZ ⊗ₖ jordanWigner m i b := rfl

/-- `m` qubits realize `2*m` Majoranas, interleaved as X,Y at each site. -/
def jordanWignerSystem (m : ℕ) :
    MajoranaSystem (m * 2) (Matrix (StandardBasis m) (StandardBasis m) ℂ) where
  ψ i := jordanWigner m (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  majorana_rel i j := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, jordanWigner_sq]
      exact one_add_one_eq_two
    · rw [if_neg hij]
      have hp : finProdFinEquiv.symm i ≠ finProdFinEquiv.symm j :=
        fun h => hij (finProdFinEquiv.symm.injective h)
      have hs : (finProdFinEquiv.symm i).1 ≠ (finProdFinEquiv.symm j).1 ∨
          (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 := by
        by_cases hfirst : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1
        · exact Or.inr (fun hsecond => hp (Prod.ext hfirst hsecond))
        · exact Or.inl hfirst
      rw [jordanWigner_anticommute m _ _ _ _ hs]
      exact neg_add_cancel _
  self_adjoint i := jordanWigner_self_adjoint m _ _

/-- The standard Jordan–Wigner realization for any even number `N` of Majoranas.
The representation space has dimension `2^(N/2)`. -/
def standardMajoranaSystem (N : ℕ) (hN : Even N) :
    MajoranaSystem N (Matrix (StandardBasis (N / 2)) (StandardBasis (N / 2)) ℂ) := by
  have hsize : N = N / 2 * 2 := by
    obtain ⟨m, hm⟩ := hN
    omega
  let M := jordanWignerSystem (N / 2)
  exact {
    ψ := fun i => M.ψ (Fin.cast hsize i)
    majorana_rel := fun i j => by simpa using M.majorana_rel (Fin.cast hsize i) (Fin.cast hsize j)
    self_adjoint := fun i => M.self_adjoint (Fin.cast hsize i)
  }

private theorem interaction_trace_eq_zero
    {N q : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (M : MajoranaSystem N (Matrix d d ℂ)) (hq : Even q)
    (A B : InteractionIndex N q) (hAB : A ≠ B) :
    Matrix.trace (M.interactionOperator A * M.interactionOperator B) = 0 := by
  classical
  have hset : A.1 ≠ B.1 := fun h => hAB (Subtype.ext h)
  have hnot : ¬ A.1 ⊆ B.1 := by
    intro hsub
    exact hset (Finset.eq_of_subset_of_card_le hsub (by rw [A.2, B.2]))
  obtain ⟨i, hiA, hiB⟩ := Finset.not_subset.mp hnot
  let X := M.interactionOperator A * M.interactionOperator B
  have hanti : X * M.ψ i = -(M.ψ i * X) := by
    dsimp [X]
    rw [mul_assoc, M.interactionOperator_mul_generator_of_not_mem hq B i hiB,
      ← mul_assoc, M.interactionOperator_mul_generator_of_mem hq A i hiA,
      neg_mul, mul_assoc]
  have hconj : M.ψ i * X * M.ψ i = -X := by
    rw [mul_assoc, hanti, mul_neg, ← mul_assoc, M.majorana_sq, one_mul]
  have hcyclic : Matrix.trace (M.ψ i * X * M.ψ i) = Matrix.trace X := by
    rw [Matrix.trace_mul_comm, ← mul_assoc, M.majorana_sq, one_mul]
  have htrace : Matrix.trace X = -Matrix.trace X := by
    calc
      Matrix.trace X = Matrix.trace (M.ψ i * X * M.ψ i) := hcyclic.symm
      _ = Matrix.trace (-X) := congrArg Matrix.trace hconj
      _ = -Matrix.trace X := Matrix.trace_neg X
  exact CharZero.eq_neg_self_iff.mp htrace

/-- The shared phase-corrected interactions in the standard representation are
orthonormal for the normalized trace inner product. No orthogonality field is
added to the abstract Majorana system. -/
theorem standardInteraction_orthonormal
    (N : ℕ) (hN : Even N) {q : ℕ} (hq : Even q)
    (A B : InteractionIndex N q) :
    normalizedTrace
      (star ((standardMajoranaSystem N hN).interactionOperator A) *
        (standardMajoranaSystem N hN).interactionOperator B) =
      if A = B then 1 else 0 := by
  classical
  let M := standardMajoranaSystem N hN
  change normalizedTrace (star (M.interactionOperator A) * M.interactionOperator B) = _
  rw [M.interactionOperator_star hq]
  by_cases hAB : A = B
  · subst B
    rw [M.interactionOperator_sq hq, normalizedTrace_one, if_pos rfl]
  · rw [if_neg hAB, normalizedTrace, interaction_trace_eq_zero M hq A B hAB, zero_div]

end SYK
