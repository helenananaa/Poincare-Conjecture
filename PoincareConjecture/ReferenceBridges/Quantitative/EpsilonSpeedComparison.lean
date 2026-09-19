import Mathlib
import PoincareConjecture.ParallelMath.Core
import ReferenceBridges.Quantitative.EpsilonMetricComparison
import PoincareConjecture.ParallelMath.Quantitative.SqrtMetric
import MorganTianLib.Ch02.EpsilonClose
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter Riemannian
open scoped BigOperators Topology Manifold ContDiff
open MorganTianLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Actual epsilon-close metrics compare tangent speeds with square-root constants. -/
theorem epsilonClose_speed_comparison {epsilon : ℝ} (g0 g : Riemannian.RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose epsilon g0 g) :
    ∀ p : M, ∀ v : TangentSpace I p,
      Real.sqrt (1-epsilon)*Real.sqrt (g0.metricInner p v v) ≤ Real.sqrt (g.metricInner p v v) ∧
      Real.sqrt (g.metricInner p v v) ≤ Real.sqrt (1+epsilon)*Real.sqrt (g0.metricInner p v v) :=
/- SWARM_PROOF_BEGIN -/
by
  intro p v
  have hcmp := epsilonClose_metric_comparison g0 g h p v
  have he0 : 0 < epsilon := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have he1 : epsilon < 1 / 2 := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.2.1
  exact sqrt_comparison_of_quadratic_bounds
    (g0.metricInner p v v) (g.metricInner p v v) epsilon
    (g0.metricInner_self_nonneg p v)
    (g.metricInner_self_nonneg p v)
    he0.le (he1.trans (by norm_num))
    hcmp.1 hcmp.2
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
