import Mathlib
import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
import PoincareConjecture.ParallelImplementation.ChartInverseDifferentialEquivalence
import PoincareConjecture.ParallelImplementation.ChartMetricPullbackPairings
import PoincareConjecture.ParallelImplementation.SmoothCoordinateBilinearOperator
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ActualChartMetricOperator
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_actual_chart_metric_operator
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) M) (p : M) :

    ∃ A : E3 → (E3 →L[ℝ] E3), ContDiffOn ℝ ∞ A (extChartAt 𝓘(ℝ, E3) p).target ∧
      (∀ y v w : E3, inner ℝ (A y v) w=g.metricInner ((extChartAt 𝓘(ℝ, E3) p).symm y) ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) v) ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) w)) ∧
      (∀ y ∈ (extChartAt 𝓘(ℝ, E3) p).target, ∀ v w : E3, inner ℝ (A y v) w=inner ℝ (A y w) v) ∧
      ∀ y ∈ (extChartAt 𝓘(ℝ, E3) p).target, ∀ v : E3, v ≠ 0 → 0 < inner ℝ (A y v) v :=
/- SWARM_PROOF_BEGIN -/
by
  rcases PoincareConjecture.ParallelImplementation.ChartMetricPullbackPairings.exists_chart_metric_pullback_pairings g p with
    ⟨b, hb, hbcont⟩
  rcases PoincareConjecture.ParallelImplementation.SmoothCoordinateBilinearOperator.exists_smooth_coordinate_bilinear_operator
      (extChartAt 𝓘(ℝ, E3) p).target b (fun i j => hbcont i j) with
    ⟨A, hA, hrep⟩
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · intro y v w
    rw [hrep y v w, hb y v w]
  · intro y hy v w
    rw [hrep y v w, hrep y w v, hb y v w, hb y w v]
    exact g.metricInner_comm ((extChartAt 𝓘(ℝ, E3) p).symm y)
      ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) v)
      ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) w)
  · intro y hy v hv
    rw [hrep y v v, hb y v v]
    obtain ⟨L, hL⟩ :=
      PoincareConjecture.ParallelImplementation.ChartInverseDifferentialEquivalence.chart_inverse_differential_equivalence
        g p y hy
    have hder :
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) v ≠ 0 := by
      intro hzero
      apply hv
      have hzL : L v = 0 := by
        rw [hL v]
        exact hzero
      apply L.injective
      simpa using hzL
    exact g.metricInner_self_pos ((extChartAt 𝓘(ℝ, E3) p).symm y)
      ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) v) hder
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ActualChartMetricOperator
