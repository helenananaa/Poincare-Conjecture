import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.Basic
import PoincareConjecture.ParallelImplementation.EuclideanCoordinateTrace
import PoincareConjecture.ParallelImplementation.IntrinsicRicciEndomorphism
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.IntrinsicRicciCoordinateTrace
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem ricci_eq_coordinate_curvature_trace
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3)
    (V : Idx → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3)
    (hV : ∀ (i : Idx) (x : E3), V i x = EuclideanSpace.single i 1) :

    ∀ (x : E3) (i j : Idx), MorganTianLib.ricciTensorAt g x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        ∑ k : Idx, (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) ((g.leviCivitaConnection.curvature (V i) (V k) (V j)) x) :=
/- SWARM_PROOF_BEGIN -/
by
  intro x i j
  obtain ⟨A, hA, hRicci⟩ :=
    PoincareConjecture.ParallelImplementation.IntrinsicRicciEndomorphism.ricci_eq_curvature_trace
      g x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [hRicci,
    PoincareConjecture.ParallelImplementation.EuclideanCoordinateTrace.trace_eq_coordinate_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hA (EuclideanSpace.single k 1)]
  rw [g.leviCivitaConnection.curvatureOperatorAt_eq x (hV i x) (hV k x) (hV j x)]
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.IntrinsicRicciCoordinateTrace
