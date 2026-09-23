import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualDeTurckLiePrincipal
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualRicciPrincipalResidual
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual local Ricci and gauge-Lie coordinate expressions differ from the elliptic principal term only quadratically in first jets.
This is a local identity estimate, not an existence theorem or intrinsic tensor identification. -/
theorem actual_deturck_coordinate_residual_bound (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G)
    (hsym : ∀ y v w : E3, inner ℝ (G y v) w=inner ℝ v (G y w))
    (x : E3) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (i j : Fin 3) :
    let C : Matrix (Fin 3) (Fin 3) ℝ := fun a b => ((G x).inverse (EuclideanSpace.single b 1)) a;
    let Q := fun a b m n : Fin 3 =>
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single b 1)) x
        (EuclideanSpace.single a 1) (EuclideanSpace.single n 1)) m;
    let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y) (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k);
    |-2*actualCoordinateRicci G x i j+coordinateLieMetricExpr G W x i j-
      (∑ p : Fin 3, ∑ q : Fin 3, C p q*Q p q i j)| ≤
      (1200/c^2)*(∑ l : Fin 3, ‖fderiv ℝ G x (EuclideanSpace.single l 1)‖)^2 :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  classical
  let P : Fin 3 → E3 →L[ℝ] E3 := fun a =>
    fderiv ℝ G x (EuclideanSpace.single a 1)
  let C : Matrix (Fin 3) (Fin 3) ℝ := fun a b =>
    ((G x).inverse (EuclideanSpace.single b 1)) a
  let Q : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun a b m n =>
    (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single b 1)) x
      (EuclideanSpace.single a 1) (EuclideanSpace.single n 1)) m
  let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
    coordinateDeTurckGauge (G y)
      (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k)
  have hSplitRaw := actual_deturck_lie_principal_split G hG hsym x c hc hpos i j
  have hSplit : coordinateLieMetricExpr G W x i j =
      (∑ p : Fin 3, ∑ q : Fin 3,
        C p q * (Q i p j q + Q j p i q - Q i j p q)) +
        deturckLieLowerOrder (G x) P i j := by
    simpa [W, C, Q, P] using hSplitRaw
  have hRicciRaw := actual_ricci_principal_residual_control G hG hsym x c hc hpos i j
  have hRicci :
      |(-2 * actualCoordinateRicci G x i j +
          (∑ p : Fin 3, ∑ q : Fin 3,
            C p q * (Q i p j q + Q j p i q - Q i j p q)) -
          (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q p q i j))| ≤
        (800 / c ^ 2) *
          (∑ l : Fin 3, ‖fderiv ℝ G x (EuclideanSpace.single l 1)‖) ^ 2 := by
    simpa [C, Q] using hRicciRaw
  have hGauge := deturck_lie_lower_order_bound (G x) P c hc hpos i j
  have hP : ∑ l : Fin 3, ‖P l‖ =
      ∑ l : Fin 3, ‖fderiv ℝ G x (EuclideanSpace.single l 1)‖ := by
    simp [P]
  calc
    |(-2 * actualCoordinateRicci G x i j +
        coordinateLieMetricExpr G W x i j -
          (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q p q i j))| =
        |(-2 * actualCoordinateRicci G x i j +
            (∑ p : Fin 3, ∑ q : Fin 3,
              C p q * (Q i p j q + Q j p i q - Q i j p q)) -
            (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q p q i j)) +
          deturckLieLowerOrder (G x) P i j| := by
            rw [hSplit]
            ring_nf
    _ ≤
        |(-2 * actualCoordinateRicci G x i j +
            (∑ p : Fin 3, ∑ q : Fin 3,
              C p q * (Q i p j q + Q j p i q - Q i j p q)) -
            (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q p q i j))| +
          |deturckLieLowerOrder (G x) P i j| := abs_add_le _ _
    _ ≤ (800 / c ^ 2) *
          (∑ l : Fin 3, ‖fderiv ℝ G x (EuclideanSpace.single l 1)‖) ^ 2 +
        (400 / c ^ 2) *
          (∑ l : Fin 3, ‖fderiv ℝ G x (EuclideanSpace.single l 1)‖) ^ 2 := by
            rw [hP] at hGauge
            exact add_le_add hRicci hGauge
    _ = (1200 / c ^ 2) *
          (∑ l : Fin 3, ‖fderiv ℝ G x (EuclideanSpace.single l 1)‖) ^ 2 := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
