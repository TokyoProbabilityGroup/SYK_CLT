import SYK.Annealed_FE.main_result

set_option autoImplicit false

/-!
# Lemma `b_v` versus `b(H)`

Lean statement of Lemma `lemma:b_v-vs-b(H)` from `refs/SYK-HT-arxiv.tex`.
The combinatorial notions that are not yet part of `SYK_model` are kept as
paper-facing abstract parameters; the model-dependent namespace and imported
objects come from `SYK_model` via `Annealed_FE.main_result`.
-/

noncomputable section

namespace SYK
namespace AnnealedFE
namespace Lemmas

/-- A multi-hypergraph placeholder for the doubled simple hypergraphs used in
Lemma `lemma:b_v-vs-b(H)`. -/
constant MultiHypergraph (v q : ℕ) : Type

/-- The doubled multi-hypergraph associated with a simple hypergraph. -/
constant doubledHypergraph {v q : ℕ} : SimpleHypergraph v q → MultiHypergraph v q

/-- The paper's multiplicity count `m(H)` for a multi-hypergraph. -/
constant multiEdgeMultiplicity {v q : ℕ} : MultiHypergraph v q → ℕ

/-- The paper's weight `b(H)` for a multi-hypergraph. -/
constant bMulti {v q : ℕ} : MultiHypergraph v q → ℂ

/-- The paper's simple-hypergraph weight `b_H`. -/
constant bSimpleHypergraph {v q : ℕ} : SimpleHypergraph v q → ℂ

/-- Lemma `lemma:b_v-vs-b(H)`: for a simple hypergraph viewed as a doubled
multi-hypergraph, the multi-hypergraph weight is the simple weight multiplied
by `m(H)! / 2^(m(H)/2)`. -/
theorem b_v_vs_bH {v q : ℕ} (H : SimpleHypergraph v q) :
    bMulti (doubledHypergraph H) =
      bSimpleHypergraph H *
        ((Nat.factorial (multiEdgeMultiplicity (doubledHypergraph H)) : ℂ) /
          (2 : ℂ) ^ (multiEdgeMultiplicity (doubledHypergraph H) / 2)) := by
  sorry

end Lemmas
end AnnealedFE
end SYK
