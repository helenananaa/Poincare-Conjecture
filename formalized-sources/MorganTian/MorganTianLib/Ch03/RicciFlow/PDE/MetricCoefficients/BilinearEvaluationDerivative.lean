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
  have h1 := hΓ.hasFDerivAt.clm_apply (hasFDerivAt_const X x)
  have h2 := h1.clm_apply (hasFDerivAt_const Y x)
  have h3 := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp x h2
  simpa [Function.comp_def] using congrArg (fun L : E3 →L[ℝ] ℝ => L v) h3.fderiv
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
