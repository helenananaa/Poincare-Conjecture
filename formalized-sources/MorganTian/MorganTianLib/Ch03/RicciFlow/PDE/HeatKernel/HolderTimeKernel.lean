import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory
open scoped Interval
noncomputable section
namespace MorganTianLib.ParabolicPDE

/-- **Math.** The actual temporal singularity of the Holder Hessian estimate
is integrable, with its exact small-time factor. -/
theorem holderTimeKernel_integrable_integral {alpha T : ℝ} (ha : 0 < alpha) :
    IntervalIntegrable (fun s : ℝ => (T - s) ^ (alpha / 2 - 1)) volume 0 T ∧
      (∫ s in (0 : ℝ)..T, (T - s) ^ (alpha / 2 - 1)) =
        (2 / alpha) * T ^ (alpha / 2) := by
  have he : -1 < alpha / 2 - 1 := by linarith
  have hint := (intervalIntegral.intervalIntegrable_rpow'
    (a := (0 : ℝ)) (b := T) he).comp_sub_left T
  refine ⟨?_, ?_⟩
  · simpa only [sub_zero, sub_self] using hint.symm
  · rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ (alpha / 2 - 1)) T]
    simp only [sub_self, sub_zero]
    rw [integral_rpow (Or.inl he)]
    have hexp : alpha / 2 - 1 + 1 = alpha / 2 := by ring
    rw [hexp, Real.zero_rpow (ne_of_gt (by linarith : 0 < alpha / 2)), sub_zero]
    field_simp

end MorganTianLib.ParabolicPDE
