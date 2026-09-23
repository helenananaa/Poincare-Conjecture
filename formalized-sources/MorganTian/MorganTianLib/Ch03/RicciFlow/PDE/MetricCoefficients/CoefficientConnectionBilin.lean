import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateConnectionVector
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
def coefficientConnectionBilin (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) : E3 →L[ℝ] E3 →L[ℝ] E3 :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
      ((EuclideanSpace.proj (𝕜 := ℝ) j).smulRight
        (coordinateChristoffel A P k i j • EuclideanSpace.single k 1))

/-- **Math.** coefficient connection bilin apply. -/
theorem coefficient_connection_bilin_apply (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3) (X Y : E3) :
    coefficientConnectionBilin A P X Y = connectionVector A P X Y :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  ext k
  simp [coefficientConnectionBilin, connectionVector,
    EuclideanSpace.proj, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
