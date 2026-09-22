import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set Function Filter
open scoped ContDiff Topology
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Exact Frechet derivative of the quadratic polynomial used in Taylor subtraction. -/
theorem symmetric_quadratic_differential (B : E3 →L[ℝ] E3 →L[ℝ] ℝ)
    (hB : ∀ v w : E3, B v w = B w v) (x z : E3) :
    HasFDerivAt (fun w : E3 => (1/2:ℝ) * B (w-x) (w-x)) (B (z-x)) z :=
/- SWARM_PROOF_BEGIN -/
by
  have htranslated : HasFDerivAt (fun w : E3 => w - x)
      (ContinuousLinearMap.id ℝ E3) z :=
    (hasFDerivAt_id z).sub_const x
  have hquadratic := B.hasFDerivAt_of_bilinear htranslated htranslated
  have hscaled := hquadratic.const_smul (1 / 2 : ℝ)
  have hderiv :
      (1 / 2 : ℝ) •
          (B.precompR E3 (z - x) (ContinuousLinearMap.id ℝ E3) +
            B.precompL E3 (ContinuousLinearMap.id ℝ E3) (z - x)) = B (z - x) := by
    ext v
    change (1 / 2 : ℝ) * (B (z - x) v + B v (z - x)) = B (z - x) v
    rw [hB v (z - x)]
    ring
  refine (hscaled.congr_fderiv hderiv).congr_of_eventuallyEq ?_
  filter_upwards [] with w
  simp only [Pi.smul_apply, smul_eq_mul]
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
