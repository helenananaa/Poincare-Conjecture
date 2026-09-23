import MorganTianLib.Ch01.CurvatureCommutation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** bilinear evaluation fderiv. -/
theorem bilinear_evaluation_fderiv (Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3) (x v X Y : E3)
    (hΓ : DifferentiableAt ℝ Γ x) (k : Fin 3) :
    fderiv ℝ (fun y : E3 => (Γ y X Y) k) x v = (fderiv ℝ Γ x v X Y) k :=
/- SWARM_PROOF_BEGIN -/
by
  let evalX : (E3 →L[ℝ] E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) :=
    ContinuousLinearMap.apply ℝ (E3 →L[ℝ] E3) X
  let evalY : (E3 →L[ℝ] E3) →L[ℝ] E3 :=
    ContinuousLinearMap.apply ℝ E3 Y
  let evalK : E3 →L[ℝ] ℝ := EuclideanSpace.proj k
  let eval : (E3 →L[ℝ] E3 →L[ℝ] E3) →L[ℝ] ℝ :=
    evalK.comp (evalY.comp evalX)
  have hcomp := eval.hasFDerivAt.comp x hΓ.hasFDerivAt
  have hderiv : fderiv ℝ (fun y : E3 => eval (Γ y)) x =
      eval.comp (fderiv ℝ Γ x) := hcomp.fderiv
  change fderiv ℝ (fun y : E3 => eval (Γ y)) x v = (fderiv ℝ Γ x v X Y) k
  rw [hderiv]
  rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
