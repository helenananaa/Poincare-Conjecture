import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.Basic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.EuclideanCoordinateTrace
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem trace_eq_coordinate_sum
    (A : E3 →ₗ[ℝ] E3) :

    LinearMap.trace ℝ E3 A = ∑ k : Idx, (A (EuclideanSpace.single k 1)) k :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rw [LinearMap.trace_eq_sum_inner A (EuclideanSpace.basisFun Idx ℝ)]
  simp [EuclideanSpace.inner_single_left]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.EuclideanCoordinateTrace
