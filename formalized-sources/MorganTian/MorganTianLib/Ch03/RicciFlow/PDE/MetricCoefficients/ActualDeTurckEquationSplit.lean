import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualDeTurckLiePrincipal
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualCoordinateRicci
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualMetricPrincipalJet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** actual deturck equation split. -/
theorem actual_deturck_equation_split (G : E3 → (E3 →L[ℝ] E3)) (hG : ContDiff ℝ 2 G)
    (hsym : ∀ y v w : E3, inner ℝ (G y v) w = inner ℝ v (G y w))
    (x : E3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (i j : Fin 3) :
    let P := fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1);
    let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y) (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k);
    -2*actualCoordinateRicci G x i j + coordinateLieMetricExpr G W x i j =
      (∑ p : Fin 3, ∑ q : Fin 3, ((G x).inverse (EuclideanSpace.single q 1)) p *
        (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single q 1)) x
          (EuclideanSpace.single p 1) (EuclideanSpace.single j 1)) i) +
      (-2*ricciLowerOrder (G x) P i j + deturckLieLowerOrder (G x) P i j) :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  rw [actual_coordinate_ricci_decomposition G hG x c hc hpos i j]
  rw [actual_deturck_lie_principal_split G hG hsym x c hc hpos i j]
  linear_combination (actual_metric_principal_jet_identity G hG hsym x c hc hpos i j)
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
