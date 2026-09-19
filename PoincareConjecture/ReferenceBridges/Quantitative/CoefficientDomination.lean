import Mathlib
import PoincareConjecture.ParallelMath.Core
import MorganTianLib.Ch02.ForwardDifference
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff

/-- **Math.** A lower bound on the curvature coefficient weakens the actual forward difference inequality. -/
theorem forwardDiff_of_coefficient_lower_bound (u q : ℝ → ℝ) (alpha c k t : ℝ)
    (hu : 0 ≤ u t) (hq : -(alpha/(t+c)) ≤ q t)
    (hd : MorganTianLib.ForwardDiffQuotientLE u t (-k-q t*u t)) :
    MorganTianLib.ForwardDiffQuotientLE u t (-k+alpha/(t+c)*u t) :=
/- SWARM_PROOF_BEGIN -/
by
  refine MorganTianLib.ForwardDiffQuotientLE.mono hd ?_
  have hq' : -q t ≤ alpha / (t + c) := by
    simpa [neg_neg] using neg_le_neg hq
  have hmul : -(q t * u t) ≤ (alpha / (t + c)) * u t := by
    simpa [neg_mul] using mul_le_mul_of_nonneg_right hq' hu
  linarith [hmul]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
