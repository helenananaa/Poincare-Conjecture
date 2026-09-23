import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricGermJets
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeVector
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateLieMetricLowering
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ

/-- **Math.** actual gauge lie germ. -/
theorem actual_gauge_lie_germ (G H : E3 → (E3 →L[ℝ] E3)) (x : E3) (h : G =ᶠ[𝓝 x] H) (i j : Fin 3) :
    let WG : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y) (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k);
    let WH : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (H y) (fun r : Fin 3 => fderiv ℝ H y (EuclideanSpace.single r 1)) k);
    coordinateLieMetricExpr G WG x i j = coordinateLieMetricExpr H WH x i j :=
/- SWARM_PROOF_BEGIN -/
by
  let WG : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
    coordinateDeTurckGauge (G y)
      (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k)
  let WH : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
    coordinateDeTurckGauge (H y)
      (fun r : Fin 3 => fderiv ℝ H y (EuclideanSpace.single r 1)) k)
  change coordinateLieMetricExpr G WG x i j = coordinateLieMetricExpr H WH x i j
  have hFderiv : (fun y : E3 => fderiv ℝ G y) =ᶠ[𝓝 x]
      (fun y : E3 => fderiv ℝ H y) := h.fderiv
  have hW : WG =ᶠ[𝓝 x] WH := by
    filter_upwards [h, hFderiv] with y hGH hDGH
    ext k
    change coordinateDeTurckGauge (G y)
        (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k =
      coordinateDeTurckGauge (H y)
        (fun r : Fin 3 => fderiv ℝ H y (EuclideanSpace.single r 1)) k
    rw [hGH, hDGH]
  have hGx : G x = H x := h.eq_of_nhds
  have hDGx : fderiv ℝ G x = fderiv ℝ H x := hFderiv.eq_of_nhds
  have hWx : WG x = WH x := hW.eq_of_nhds
  have hDWx : fderiv ℝ WG x = fderiv ℝ WH x := hW.fderiv.eq_of_nhds
  unfold coordinateLieMetricExpr
  rw [hGx, hDGx, hWx, hDWx]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
