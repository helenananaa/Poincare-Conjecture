import Mathlib
import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
import PoincareConjecture.ParallelImplementation.EuclideanPositiveOperatorMetric
import PoincareConjecture.ParallelImplementation.OpenPositiveOperatorExtension
import PoincareConjecture.ParallelImplementation.ActualChartMetricOperator
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ChartMetricEuclideanExtension
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_chart_metric_euclidean_extension
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) M) (p : M) :

    ∃ rho : ℝ, 0 < rho ∧ Metric.closedBall ((extChartAt 𝓘(ℝ, E3) p) p) rho ⊆ (extChartAt 𝓘(ℝ, E3) p).target ∧
    ∃ h : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3,
      ∀ y ∈ Metric.closedBall ((extChartAt 𝓘(ℝ, E3) p) p) rho, ∀ v w : E3, h.metricInner y v w=g.metricInner ((extChartAt 𝓘(ℝ, E3) p).symm y) ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) v) ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) w) :=
/- SWARM_PROOF_BEGIN -/
by
  rcases PoincareConjecture.ParallelImplementation.ActualChartMetricOperator.exists_actual_chart_metric_operator
      g p with ⟨A, hA, hrep, hsym, hpos⟩
  let φ := extChartAt 𝓘(ℝ, E3) p
  have hp : φ p ∈ φ.target := mem_extChartAt_target p
  have hopen : IsOpen φ.target := isOpen_extChartAt_target p
  rcases PoincareConjecture.ParallelImplementation.OpenPositiveOperatorExtension.exists_open_positive_operator_extension
      φ.target hopen (φ p) hp A hA hsym hpos with
    ⟨rho, hrho, hball, B, hB, hBeq, _hBcompact, hBsym, hBpos⟩
  rcases PoincareConjecture.ParallelImplementation.EuclideanPositiveOperatorMetric.exists_positive_operator_metric
      B hB hBsym hBpos with ⟨h, hh⟩
  refine ⟨rho, hrho, hball, h, ?_⟩
  intro y hy v w
  rw [hh, hBeq y hy]
  exact hrep y v w
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ChartMetricEuclideanExtension
