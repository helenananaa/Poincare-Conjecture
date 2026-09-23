import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BackgroundLieCorrection
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateLieSubtraction
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualDeTurckEquationSplit
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualGaugeDifferentiable
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** background deturck equation split. -/
theorem background_deturck_equation_split (G : E3 → (E3 →L[ℝ] E3)) (T : E3 → T3) (hG : ContDiff ℝ 2 G)
    (hsym : ∀ y v w : E3, inner ℝ (G y v) w=inner ℝ v (G y w))
    (x : E3) (hT : DifferentiableAt ℝ T x) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (i j : Fin 3) :
    let P := fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1);
    let R := fun r k a b : Fin 3 => fderiv ℝ (fun y => T y k a b) x (EuclideanSpace.single r 1);
    let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y) (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k);
    -2*actualCoordinateRicci G x i j +
      coordinateLieMetricExpr G (fun y => W y-backgroundConnectionContraction (G y) (T y)) x i j =
      (∑ p : Fin 3, ∑ q : Fin 3, ((G x).inverse (EuclideanSpace.single q 1)) p *
        (fderiv ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single q 1)) x
          (EuclideanSpace.single p 1) (EuclideanSpace.single j 1)) i) +
      (-2*ricciLowerOrder (G x) P i j + deturckLieLowerOrder (G x) P i j -
        backgroundLieCorrection (G x) P (T x) R i j) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let P := fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)
  let R := fun r k a b : Fin 3 =>
    fderiv ℝ (fun y => T y k a b) x (EuclideanSpace.single r 1)
  let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
    coordinateDeTurckGauge (G y)
      (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k)
  let Z : E3 → E3 := fun y => backgroundConnectionContraction (G y) (T y)
  have hGdiff : DifferentiableAt ℝ G x :=
    hG.contDiffAt.differentiableAt (by norm_num)
  have hWdiff : DifferentiableAt ℝ W x := by
    simpa [W] using actual_deturck_gauge_differentiable G hG x c hc hpos
  have hZdiff : DifferentiableAt ℝ Z x := by
    have hB := background_connection_contraction_smooth (G x) (T x) c hc hpos
    have hPair : DifferentiableAt ℝ (fun y : E3 => (G y, T y)) x :=
      hGdiff.prodMk hT
    exact DifferentiableAt.comp
      (f := fun y : E3 => (G y, T y))
      (g := fun z : (E3 →L[ℝ] E3) × T3 => backgroundConnectionContraction z.1 z.2)
      x (hB.differentiableAt (by norm_num)) hPair
  have hsub := coordinate_lie_subtraction G W Z x hWdiff hZdiff i j
  have hbg := background_lie_first_order G T x hGdiff hT c hc hpos i j
  have hactual := actual_deturck_equation_split G hG hsym x c hc hpos i j
  have hsplit :
      -2 * actualCoordinateRicci G x i j + coordinateLieMetricExpr G W x i j =
        (∑ p : Fin 3, ∑ q : Fin 3, ((G x).inverse (EuclideanSpace.single q 1)) p *
          (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single q 1)) x
            (EuclideanSpace.single p 1) (EuclideanSpace.single j 1)) i) +
        (-2 * ricciLowerOrder (G x) P i j + deturckLieLowerOrder (G x) P i j) := by
    simpa [P, W] using hactual
  have hbg' :
      coordinateLieMetricExpr G Z x i j = backgroundLieCorrection (G x) P (T x) R i j := by
    simpa [P, R, Z] using hbg
  calc
    -2 * actualCoordinateRicci G x i j +
        coordinateLieMetricExpr G (fun y => W y - Z y) x i j =
        (-2 * actualCoordinateRicci G x i j + coordinateLieMetricExpr G W x i j) -
          backgroundLieCorrection (G x) P (T x) R i j := by
            rw [hsub, hbg']
            ring
    _ = (∑ p : Fin 3, ∑ q : Fin 3, ((G x).inverse (EuclideanSpace.single q 1)) p *
          (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single q 1)) x
            (EuclideanSpace.single p 1) (EuclideanSpace.single j 1)) i) +
        (-2 * ricciLowerOrder (G x) P i j + deturckLieLowerOrder (G x) P i j -
          backgroundLieCorrection (G x) P (T x) R i j) := by
            rw [hsplit]
            ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
