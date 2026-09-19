import ReferenceBridges.GlobalTransfer.Core
set_option autoImplicit false
noncomputable section
open PoincareConjecture.ParallelMath.Transfer Riemannian Manifold
open scoped Bundle Manifold ContDiff
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
 (g0 g1 : RiemannianMetric I M) : True := by
 fail_if_success have bad : metricPathLength g0 = metricPathLength g1 := rfl
 fail_if_success have bad : metricEDist g0 = metricEDist g1 := rfl
 have _ := g0
 have _ := g1
 trivial
