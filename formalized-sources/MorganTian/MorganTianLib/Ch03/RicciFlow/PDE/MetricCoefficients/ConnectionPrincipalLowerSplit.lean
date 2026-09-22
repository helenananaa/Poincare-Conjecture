import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LowerConnectionJet
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateConnectionFieldDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckPrincipalJet
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Exact separation of second jets and first-jet quadratic terms in actual spatial differentiation. -/
theorem connection_principal_lower_split (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G) (x : E3) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (r k i j : Fin 3) :
    let P := fun a : Fin 3 => fderiv ℝ G x (EuclideanSpace.single a 1)
    let C : Matrix (Fin 3) (Fin 3) ℝ := fun a b => ((G x).inverse (EuclideanSpace.single b 1)) a
    let Q := fun a b m n : Fin 3 =>
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single b 1)) x
        (EuclideanSpace.single a 1) (EuclideanSpace.single n 1)) m
    fderiv ℝ (fun y : E3 => coordinateChristoffel (G y)
      (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k i j) x (EuclideanSpace.single r 1) =
      principalConnectionJet C Q r k i j+lowerConnectionJet (G x) P r k i j :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  have hderiv := coordinate_connection_field_derivative G hG x (EuclideanSpace.single r 1)
    c hc hpos k i j
  rw [hderiv]
  unfold principalConnectionJet lowerConnectionJet
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]
  ring_nf
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
