import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

open Filter
open scoped Topology

namespace SYK
namespace CLT

/--
Convex convergence implies derivative convergence.

This is Lemma 2.1 from the blueprint.  The open interval is represented by an
open set `I`; convexity of `I` is included in each `ConvexOn` hypothesis.  The
assumption that the limit is $C^1$ is encoded as differentiability on `I` and
continuity of `deriv F` on `I`.
-/
theorem convex_convergence_deriv_tendstoUniformlyOn
    {I K : Set ℝ} {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hI : IsOpen I)
    (hconv : ∀ n, ConvexOn ℝ I (f n))
    (hfdiff : ∀ n x, x ∈ I → DifferentiableAt ℝ (f n) x)
    (hlim : TendstoLocallyUniformlyOn f F atTop I)
    (hFdiff : ∀ x, x ∈ I → DifferentiableAt ℝ F x)
    (hFderiv_cont : ContinuousOn (fun x => deriv F x) I)
    (hK : IsCompact K)
    (hKI : K ⊆ I) :
    TendstoUniformlyOn (fun n x => deriv (f n) x) (fun x => deriv F x) atTop K := by
  classical
  -- Choose a closed metric thickening of `K` contained in the interval.
  obtain ⟨δ, hδ_pos, hδI⟩ := hK.exists_cthickening_subset_open hI hKI
  -- On this thickening the convergence is uniform, and `deriv F` is uniformly continuous.
  have hδ_compact : IsCompact (cthickening δ K) := hK.cthickening
  have hδ_uniform :
      TendstoUniformlyOn f F atTop (cthickening δ K) := by
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hδ_compact).mp
      (hlim.mono hδI)
  have hFderiv_uniform :
      UniformContinuousOn (fun x => deriv F x) (cthickening δ K) := by
    exact hδ_compact.uniformContinuousOn_of_continuous (hFderiv_cont.mono hδI)
  -- The remaining argument is the standard secant squeeze from convexity:
  -- for `x ∈ K` and small positive `h`, the derivative of `f n` at `x` lies
  -- between the left and right secant slopes.  Uniform convergence controls
  -- those slopes, while uniform continuity of `deriv F` controls the two
  -- deterministic difference quotients for `F`.
  sorry

end CLT
end SYK
