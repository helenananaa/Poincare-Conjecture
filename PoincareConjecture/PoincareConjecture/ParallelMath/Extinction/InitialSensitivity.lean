import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- Exact initial data and sensitivity to initial width, before any geometric interpretation. -/
theorem comparisonSolution_initial_and_sensitivity (q : ℝ → ℝ) (k a s : ℝ) :
    comparisonSolution q k a s s = a ∧
    ∀ a' t : ℝ, comparisonSolution q k a' s t - comparisonSolution q k a s t =
      (a'-a)*Real.exp (-rateIntegral q s t) :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · -- `∫_s^s = 0`, so the exponential prefactor is `1` and the integral term vanishes.
    simp [comparisonSolution, rateIntegral]
  · -- Difference of initial data factors through the common integrating factor.
    intro a' t
    simp only [comparisonSolution]
    ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
