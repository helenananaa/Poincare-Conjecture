import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OperatorTwoSidedInverse
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem two_sided_inverse_is_canonical
    (A b : E3 →L[ℝ] E3) (hab : A*b=1) (hba : b*A=1) :

    IsUnit A ∧ b = Ring.inverse A :=
/- SWARM_PROOF_BEGIN -/
by
  let u : (E3 →L[ℝ] E3)ˣ := ⟨A, b, hab, hba⟩
  have hA : IsUnit A := ⟨u, rfl⟩
  refine ⟨hA, ?_⟩
  calc
    b = b * (A * Ring.inverse A) := by
      rw [Ring.mul_inverse_cancel A hA, mul_one]
    _ = (b * A) * Ring.inverse A := by rw [mul_assoc]
    _ = Ring.inverse A := by rw [hba, one_mul]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OperatorTwoSidedInverse
