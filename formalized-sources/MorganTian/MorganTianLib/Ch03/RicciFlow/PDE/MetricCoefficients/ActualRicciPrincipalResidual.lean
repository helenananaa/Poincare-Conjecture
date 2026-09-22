import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualCoordinateRicci
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualMetricPrincipalJet
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Exact coordinate principal cancellation leaves a first-jet quadratic residual.
This corrects only the principal gauge part, not an already constructed full Lie derivative. -/
theorem actual_ricci_principal_residual_control (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G)
    (hsym : ∀ y v w : E3, inner ℝ (G y v) w=inner ℝ v (G y w))
    (x : E3) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (i j : Fin 3) :
    let C : Matrix (Fin 3) (Fin 3) ℝ := fun a b => ((G x).inverse (EuclideanSpace.single b 1)) a
    let Q := fun a b m n : Fin 3 =>
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single b 1)) x
        (EuclideanSpace.single a 1) (EuclideanSpace.single n 1)) m
    |-2*actualCoordinateRicci G x i j+
      (∑ p : Fin 3, ∑ q : Fin 3, C p q*(Q i p j q+Q j p i q-Q i j p q))-
      (∑ p : Fin 3, ∑ q : Fin 3, C p q*Q p q i j)| ≤
      (800/c^2)*(∑ l : Fin 3, ‖fderiv ℝ G x (EuclideanSpace.single l 1)‖)^2 :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  classical
  have hprincipal :=
    actual_metric_principal_jet_identity G hG hsym x c hc hpos i j
  dsimp at hprincipal
  have hdecomp :=
    actual_coordinate_ricci_decomposition G hG x c hc hpos i j
  dsimp at hdecomp
  have hlower :=
    ricci_lower_order_bound (G x)
      (fun a : Fin 3 => fderiv ℝ G x (EuclideanSpace.single a 1))
      c hc hpos i j
  calc
    abs (-2 * actualCoordinateRicci G x i j +
        (∑ p : Fin 3, ∑ q : Fin 3,
          ((G x).inverse (EuclideanSpace.single q 1)) p *
            ((fderiv ℝ
                (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single p 1)) x
                (EuclideanSpace.single i 1) (EuclideanSpace.single q 1)) j +
              (fderiv ℝ
                (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single p 1)) x
                (EuclideanSpace.single j 1) (EuclideanSpace.single q 1)) i -
              (fderiv ℝ
                (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single j 1)) x
                (EuclideanSpace.single i 1) (EuclideanSpace.single q 1)) p)) -
        (∑ p : Fin 3, ∑ q : Fin 3,
          ((G x).inverse (EuclideanSpace.single q 1)) p *
            (fderiv ℝ
              (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single q 1)) x
              (EuclideanSpace.single p 1) (EuclideanSpace.single j 1)) i))
        = abs (-2 * ricciLowerOrder (G x)
            (fun a : Fin 3 => fderiv ℝ G x (EuclideanSpace.single a 1)) i j) := by
          rw [hdecomp, ← hprincipal]
          congr 1
          ring
    _ = 2 * abs (ricciLowerOrder (G x)
        (fun a : Fin 3 => fderiv ℝ G x (EuclideanSpace.single a 1)) i j) := by
          rw [abs_mul]
          norm_num
    _ ≤ 2 * ((400 / c ^ 2) *
        (∑ l : Fin 3, ‖fderiv ℝ G x (EuclideanSpace.single l 1)‖) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hlower (by norm_num)
    _ = (800 / c ^ 2) *
        (∑ l : Fin 3, ‖fderiv ℝ G x (EuclideanSpace.single l 1)‖) ^ 2 := by
          ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
