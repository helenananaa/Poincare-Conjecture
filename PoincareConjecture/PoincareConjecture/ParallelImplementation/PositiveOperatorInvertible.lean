import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.PositiveOperatorInvertible
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem positive_operator_isUnit
    (A : E3 →L[ℝ] E3) (hpos : ∀ v : E3, v ≠ 0 → 0 < inner ℝ (A v) v) :

    IsUnit A :=
/- SWARM_PROOF_BEGIN -/
by
  have hinj : Function.Injective A.toLinearMap := by
    intro x y hxy
    change A x = A y at hxy
    have hzero : A (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    by_contra hne
    have hp := hpos (x - y) (sub_ne_zero.mpr hne)
    simp [hzero] at hp
  have hsurj : Function.Surjective A.toLinearMap :=
    LinearMap.surjective_of_injective hinj
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, hsurj⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.PositiveOperatorInvertible
