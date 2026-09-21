import Mathlib

open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace MorganTianLib.ParabolicPDE

/-- **Math.** The explicit one-dimensional Gaussian heat kernel. Every analytic
statement below uses positive time; no parabolic solver is assumed. -/
def gaussianHeatKernel (t x : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(x ^ 2) / (4 * t))

/-- **Math.** An explicit scalar expression, to be identified with the actual
second spatial derivative before using it in parabolic estimates. -/
def gaussianHeatHessian (t x : ℝ) : ℝ :=
  (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x

/-- **Math.** Positivity of the constructed Gaussian for every positive time. -/
theorem gaussianHeatKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 < gaussianHeatKernel t x := by
  unfold gaussianHeatKernel
  apply mul_pos
  · apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  · exact Real.exp_pos _

end MorganTianLib.ParabolicPDE
