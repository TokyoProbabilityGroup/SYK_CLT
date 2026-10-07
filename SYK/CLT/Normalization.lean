import SYK.CLT.FiniteModel
import SYK.Model.StandardRepresentation

/-!
# Manuscript trace normalization

This finite correspondence check specializes the abstract partition function to
the standard representation. The abstract CLT modules do not import this module.
-/

namespace SYK.CLT

/-- Specializing the existing definition gives the trace normalization in
`subsec:SYK-model`; this does not assert representation independence. -/
theorem partitionFunction_standard (P : Params) (hN : Even P.N) (z : ℂ)
    (g : CouplingSpace P.N P.q) :
    partitionFunction P (standardMajoranaSystem P.N hN) z g =
      ((2 : ℂ) ^ (P.N / 2))⁻¹ *
        SYK.partitionFunction z
          (normalizedHamiltonian P (standardMajoranaSystem P.N hN) g) := by
  rw [partitionFunction_eq_trace_div_card, standardBasis_card]
  simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_comm]


end SYK.CLT
