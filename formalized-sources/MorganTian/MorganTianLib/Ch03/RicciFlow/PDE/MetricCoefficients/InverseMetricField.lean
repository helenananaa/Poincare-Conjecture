import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseQuadraticRemainder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PrincipalPartDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Actual derivative of the inverse of a spatially varying metric coefficient. -/
theorem inverse_metric_field_differential (g : E3 → E3 →L[ℝ] E3) (x : E3)
    (hg : ContDiffAt ℝ ∞ g x) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (g x v) v) :
    ContDiffAt ℝ ∞ (fun y : E3 => (g y).inverse) x ∧ ∀ v : E3,
      fderiv ℝ (fun y : E3 => (g y).inverse) x v =
      -((g x).inverse.comp ((fderiv ℝ g x v).comp (g x).inverse)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨hinv, dhin⟩ := coercive_inverse_differential (g x) c hc hpos
  constructor
  · exact hinv.comp x hg
  intro v
  have hcomp :=
    ((hinv.differentiableAt (by simp)).hasFDerivAt.comp x
      (hg.differentiableAt (by simp)).hasFDerivAt).fderiv
  have hcomp' := congrArg (fun L => L v) hcomp
  simp only [ContinuousLinearMap.comp_apply] at hcomp'
  rw [dhin] at hcomp'
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using hcomp'
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
