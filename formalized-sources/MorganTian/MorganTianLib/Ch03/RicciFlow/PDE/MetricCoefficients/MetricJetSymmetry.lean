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
/-- The actual derivative of a self-adjoint metric field is self-adjoint. -/
theorem metric_jet_selfadjoint (G : E3 → (E3 →L[ℝ] E3)) (x : E3)
    (hG : DifferentiableAt ℝ G x)
    (hsym : ∀ y v w : E3, inner ℝ (G y v) w = inner ℝ v (G y w)) :
    ∀ h v w : E3, inner ℝ ((fderiv ℝ G x h) v) w =
      inner ℝ v ((fderiv ℝ G x h) w) :=
/- SWARM_PROOF_BEGIN -/
by
  intro h v w
  have hfun : (fun y : E3 => inner ℝ (G y v) w) =
      (fun y : E3 => inner ℝ v (G y w)) := by
    funext y
    exact hsym y v w
  have hfd := congrArg (fun F : E3 → ℝ => fderiv ℝ F x h) hfun
  rw [fderiv_inner_apply ℝ (hG.clm_apply (differentiableAt_const (c := v)))
      (differentiableAt_const (c := w)) h,
    fderiv_inner_apply ℝ (differentiableAt_const (c := v))
      (hG.clm_apply (differentiableAt_const (c := w))) h] at hfd
  rw [fderiv_clm_apply hG (differentiableAt_const (c := v)),
    fderiv_clm_apply hG (differentiableAt_const (c := w))] at hfd
  simpa using hfd
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
