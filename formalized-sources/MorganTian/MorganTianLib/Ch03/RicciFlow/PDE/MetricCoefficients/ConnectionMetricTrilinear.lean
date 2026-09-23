import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricTrilinearExtension
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConnectionMetricBasis
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateConnectionVector
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateMetricCompatibility
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The coordinate metric-compatibility identity extended to three arbitrary vectors. -/
theorem connection_metric_trilinear (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hsym : ∀ v w : E3, inner ℝ (A v) w=inner ℝ v (A w))
    (hP : ∀ r : Fin 3, ∀ v w : E3, inner ℝ (P r v) w=inner ℝ v (P r w))
    (X Y Z : E3) :
    inner ℝ ((∑ r : Fin 3, X r • P r) Y) Z =
      inner ℝ (A (connectionVector A P X Y)) Z +
      inner ℝ (A Y) (connectionVector A P X Z) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨B, hB, _hBbound⟩ := connection_vector_bilinear A P c hc hA
  rw [← hB X Y, ← hB X Z]
  exact metric_trilinear_extension A P B (by
    intro r i j
    rw [hB (EuclideanSpace.single r 1) (EuclideanSpace.single i 1),
      hB (EuclideanSpace.single r 1) (EuclideanSpace.single j 1)]
    exact connection_metric_basis A P c hc hA hsym hP r i j) X Y Z
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
