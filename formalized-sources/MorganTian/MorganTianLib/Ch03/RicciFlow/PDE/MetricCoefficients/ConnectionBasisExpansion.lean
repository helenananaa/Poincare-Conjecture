import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateConnectionVector
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Evaluate the coordinate connection on two standard basis vectors. -/
theorem connection_vector_basis_expansion (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (r j : Fin 3) :
    connectionVector A P (EuclideanSpace.single r 1) (EuclideanSpace.single j 1) =
      ∑ k : Fin 3, coordinateChristoffel A P k r j • EuclideanSpace.single k 1 :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  ext k
  simp [connectionVector, EuclideanSpace.single_apply, Pi.single_apply]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
