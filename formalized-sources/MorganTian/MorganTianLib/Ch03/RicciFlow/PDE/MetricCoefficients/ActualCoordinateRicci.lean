import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConnectionPrincipalLowerSplit
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.RicciLowerOrder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Coordinate Ricci expression, using actual derivatives rather than symbolic jet variables. -/
def actualCoordinateRicci (G : E3 → (E3 →L[ℝ] E3)) (x : E3) (i j : Fin 3) : ℝ :=
    (∑ k : Fin 3,
      (fderiv ℝ (fun y : E3 => coordinateChristoffel (G y)
        (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k i j) x (EuclideanSpace.single k 1)-
       fderiv ℝ (fun y : E3 => coordinateChristoffel (G y)
        (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k i k) x (EuclideanSpace.single j 1)))+
      quadraticRicciProduct (G x) (fun a : Fin 3 => fderiv ℝ G x (EuclideanSpace.single a 1)) i j
/-- Exact separation of actual second-order and lower-order terms. Geometric tensor identification is separate. -/
theorem actual_coordinate_ricci_decomposition (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G) (x : E3) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (i j : Fin 3) :
    let C : Matrix (Fin 3) (Fin 3) ℝ := fun a b => ((G x).inverse (EuclideanSpace.single b 1)) a
    let Q := fun a b m n : Fin 3 =>
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single b 1)) x
        (EuclideanSpace.single a 1) (EuclideanSpace.single n 1)) m
    actualCoordinateRicci G x i j =
      (∑ k : Fin 3, (principalConnectionJet C Q k k i j-principalConnectionJet C Q j k i k))+
        ricciLowerOrder (G x) (fun a : Fin 3 => fderiv ℝ G x (EuclideanSpace.single a 1)) i j :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp [actualCoordinateRicci]
  simp_rw [connection_principal_lower_split G hG x c hc hpos]
  unfold ricciLowerOrder
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sub_add_eq_add_sub]
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
