import Mathlib
import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff

/-- **Math.** Two-sided quadratic comparison gives the correct square-root speed bounds. -/
theorem sqrt_comparison_of_quadratic_bounds (a b epsilon : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    (hlo : (1-epsilon)*a ≤ b) (hhi : b ≤ (1+epsilon)*a) :
    Real.sqrt (1-epsilon)*Real.sqrt a ≤ Real.sqrt b ∧
    Real.sqrt b ≤ Real.sqrt (1+epsilon)*Real.sqrt a :=
/- SWARM_PROOF_BEGIN -/
by
  have h1me : 0 ≤ 1 - epsilon := sub_nonneg.mpr he1.le
  have h1pe : 0 ≤ 1 + epsilon := add_nonneg zero_le_one he0
  constructor
  · rw [← Real.sqrt_mul h1me]
    exact (Real.sqrt_le_sqrt_iff hb).mpr hlo
  · rw [← Real.sqrt_mul h1pe]
    exact (Real.sqrt_le_sqrt_iff (mul_nonneg h1pe ha)).mpr hhi
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative
