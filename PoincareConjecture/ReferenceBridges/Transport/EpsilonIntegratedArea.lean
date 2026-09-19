import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import ReferenceBridges.Quantitative.EpsilonMetricComparison
import MorganTianLib.Ch02.EpsilonClose
import ReferenceBridges.Transport.EpsilonArbitraryPair
import PoincareConjecture.ParallelMath.Transport.DominatedIntegrability

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport.Reference
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Actual metric closeness transfers finite parametrized area, without requiring target integrability separately. -/
theorem epsilonClose_integrated_pair_area {epsilon : ℝ}
    (g0 g : Riemannian.RiemannianMetric I M) (h : MorganTianLib.EpsilonClose epsilon g0 g)
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (p : Omega → M) (v w : ∀ z, TangentSpace I (p z))
    (hf : Integrable (fun z => Real.sqrt (g0.metricInner (p z) (v z) (v z)*g0.metricInner (p z) (w z) (w z)-(g0.metricInner (p z) (v z) (w z))^2)) mu)
    (hg : AEStronglyMeasurable (fun z => Real.sqrt (g.metricInner (p z) (v z) (v z)*g.metricInner (p z) (w z) (w z)-(g.metricInner (p z) (v z) (w z))^2)) mu) :
    Integrable (fun z => Real.sqrt (g.metricInner (p z) (v z) (v z)*g.metricInner (p z) (w z) (w z)-(g.metricInner (p z) (v z) (w z))^2)) mu ∧
      (1-epsilon)*(∫ z, Real.sqrt (g0.metricInner (p z) (v z) (v z)*g0.metricInner (p z) (w z) (w z)-(g0.metricInner (p z) (v z) (w z))^2) ∂mu) ≤ (∫ z, Real.sqrt (g.metricInner (p z) (v z) (v z)*g.metricInner (p z) (w z) (w z)-(g.metricInner (p z) (v z) (w z))^2) ∂mu) ∧
      (∫ z, Real.sqrt (g.metricInner (p z) (v z) (v z)*g.metricInner (p z) (w z) (w z)-(g.metricInner (p z) (v z) (w z))^2) ∂mu) ≤ (1+epsilon)*(∫ z, Real.sqrt (g0.metricInner (p z) (v z) (v z)*g0.metricInner (p z) (w z) (w z)-(g0.metricInner (p z) (v z) (w z))^2) ∂mu) :=
/- SWARM_PROOF_BEGIN -/
by
  have he0 : 0 < epsilon := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have hehalf : epsilon < 1 / 2 := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.2.1
  have hl : 0 ≤ 1 - epsilon :=
    sub_nonneg.mpr (hehalf.trans (by norm_num : (1 : ℝ) / 2 < 1)).le
  have hlu : 1 - epsilon ≤ 1 + epsilon := by linarith [he0.le]
  refine PoincareConjecture.ParallelMath.Transport.integrable_twoSided_from_reference
    mu
    (fun z => Real.sqrt (g0.metricInner (p z) (v z) (v z) * g0.metricInner (p z) (w z) (w z)
      - (g0.metricInner (p z) (v z) (w z)) ^ 2))
    (fun z => Real.sqrt (g.metricInner (p z) (v z) (v z) * g.metricInner (p z) (w z) (w z)
      - (g.metricInner (p z) (v z) (w z)) ^ 2))
    hf hg (1 - epsilon) (1 + epsilon) hl hlu ?hn ?hpt
  · exact Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _
  · exact Filter.Eventually.of_forall fun z =>
      epsilonClose_arbitrary_pair_area g0 g h (p z) (v z) (w z)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport.Reference
