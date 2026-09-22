import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffelDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateMetricCompatibility
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffelSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricInverseBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Coordinate coefficients formed from an actual C2 metric field have the explicit first derivative. -/
theorem coordinate_connection_field_derivative (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G) (x h : E3) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (k i j : Fin 3) :
    let P := fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)
    let H := fderiv ℝ G x h
    let R := fun r : Fin 3 => fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single r 1)) x h
    fderiv ℝ (fun y : E3 => coordinateChristoffel (G y)
      (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k i j) x h =
      (1/2:ℝ)*∑ l : Fin 3,
        (((-((G x).inverse.comp (H.comp (G x).inverse))) (EuclideanSpace.single l 1)) k *
          ((P i (EuclideanSpace.single l 1)) j+(P j (EuclideanSpace.single l 1)) i-(P l (EuclideanSpace.single j 1)) i) +
        ((G x).inverse (EuclideanSpace.single l 1)) k *
          ((R i (EuclideanSpace.single l 1)) j+(R j (EuclideanSpace.single l 1)) i-(R l (EuclideanSpace.single j 1)) i)) :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  classical
  have hGx : ContDiffAt ℝ 2 G x := hG.contDiffAt
  have hG1 : ContDiffAt ℝ 1 (fderiv ℝ G) x :=
    hGx.fderiv_right (m := 1) (by norm_num)
  have hGdiff : HasFDerivAt G (fderiv ℝ G x) x :=
    hGx.differentiableAt (by norm_num) |>.hasFDerivAt
  have hD2 : HasFDerivAt (fderiv ℝ G)
      (fderiv ℝ (fderiv ℝ G) x) x :=
    (hG1.differentiableAt (by norm_num)).hasFDerivAt
  have hPder : HasFDerivAt
      (fun y : E3 => fun r : Fin 3 =>
        fderiv ℝ G y (EuclideanSpace.single r 1))
      (ContinuousLinearMap.pi fun r : Fin 3 =>
        (fderiv ℝ (fderiv ℝ G) x).flip (EuclideanSpace.single r 1)) x := by
    apply hasFDerivAt_pi.2
    intro r
    simpa using hD2.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single r (1 : ℝ)) x)
  let D : E3 →L[ℝ]
      ((E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)) :=
    (fderiv ℝ G x).prod
      (ContinuousLinearMap.pi fun r : Fin 3 =>
        (fderiv ℝ (fderiv ℝ G) x).flip (EuclideanSpace.single r 1))
  have hPair : HasFDerivAt
      (fun y : E3 =>
        (G y, fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1))) D x := by
    exact hGdiff.prodMk hPder
  have hR : ∀ r : Fin 3,
      fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single r 1)) x =
        (fderiv ℝ (fderiv ℝ G) x).flip (EuclideanSpace.single r 1) := by
    intro r
    simpa using (hD2.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single r (1 : ℝ)) x)).fderiv
  have hDeval : D h =
      (fderiv ℝ G x h,
        fun r : Fin 3 =>
          fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single r 1)) x h) := by
    ext <;> simp [D, hR]
  have hC : HasFDerivAt
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        coordinateChristoffel q.1 q.2 k i j)
      (fderiv ℝ (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        coordinateChristoffel q.1 q.2 k i j) (G x,
          fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)))
      (G x, fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) := by
    exact (coordinate_christoffel_smooth (G x) c hc hpos
      (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) k i j).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hchain := hC.comp x hPair
  have hdiff := coordinate_christoffel_differential (G x)
    (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) c hc hpos k i j
    (fderiv ℝ G x h)
    (fun r : Fin 3 =>
      fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single r 1)) x h)
  have hchain' :
      fderiv ℝ (fun y : E3 => coordinateChristoffel (G y)
        (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k i j) x =
        (fderiv ℝ (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          coordinateChristoffel q.1 q.2 k i j)
          (G x, fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1))).comp D := by
    simpa [Function.comp_def] using hchain.fderiv
  rw [hchain', ContinuousLinearMap.comp_apply, hDeval]
  exact hdiff
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
