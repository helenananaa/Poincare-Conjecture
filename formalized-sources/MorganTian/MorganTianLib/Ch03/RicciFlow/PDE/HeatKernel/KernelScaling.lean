import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Basic

noncomputable section
namespace MorganTianLib.ParabolicPDE

/-- **Math.** Exact positive-time scaling of the explicit Gaussian kernel. -/
theorem gaussianHeatKernel_sqrt_scale {t : ℝ} (ht : 0 < t) (y : ℝ) :
    gaussianHeatKernel t (Real.sqrt t * y) =
      (Real.sqrt t)⁻¹ * gaussianHeatKernel 1 y := by
  have hroot : Real.sqrt (4 * Real.pi * t) =
      Real.sqrt (4 * Real.pi) * Real.sqrt t :=
    Real.sqrt_mul (by positivity) t
  have hexp : -((Real.sqrt t * y) ^ 2) / (4 * t) = -(y ^ 2) / 4 := by
    rw [mul_pow, Real.sq_sqrt ht.le]
    field_simp
    <;> ring
  unfold gaussianHeatKernel
  rw [hroot, hexp]
  simp only [mul_one, mul_inv_rev]
  ring

/-- **Math.** Exact scaling of the explicit Hessian expression; its identification
with the actual derivative is separately supplied by Equation.lean. -/
theorem gaussianHeatHessian_sqrt_scale {t : ℝ} (ht : 0 < t) (y : ℝ) :
    gaussianHeatHessian t (Real.sqrt t * y) =
      (t * Real.sqrt t)⁻¹ * gaussianHeatHessian 1 y := by
  unfold gaussianHeatHessian
  rw [gaussianHeatKernel_sqrt_scale ht, mul_pow, Real.sq_sqrt ht.le]
  simp only [one_pow, mul_one]
  field_simp
  <;> ring

end MorganTianLib.ParabolicPDE
