import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace MorganTianLib.ParabolicPDE
/-- **Math.** Exact derivatives and the heat equation for the explicit Gaussian. -/
theorem gaussianHeatKernel_derivatives {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (gaussianHeatKernel t) ∧ ∀ x : ℝ,
      deriv (gaussianHeatKernel t) x = -(x / (2 * t)) * gaussianHeatKernel t x ∧
      iteratedDeriv 2 (gaussianHeatKernel t) x = gaussianHeatHessian t x ∧
      deriv (fun s => gaussianHeatKernel s x) t = gaussianHeatHessian t x := by
/- SWARM_PROOF_BEGIN -/
  have htime_ne : t ≠ 0 := ne_of_gt ht
  have htime_pos : 0 < 4 * Real.pi * t := by
    positivity
  have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi * t) :=
    Real.sqrt_pos.2 htime_pos
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := ne_of_gt hsqrt_pos
  have hcont : ContDiff ℝ ∞ (gaussianHeatKernel t) := by
    unfold gaussianHeatKernel
    fun_prop
  have hE_spatial : ∀ y : ℝ,
      HasDerivAt (fun z : ℝ => -(z ^ 2) / (4 * t)) (-(y / (2 * t))) y := by
    intro y
    have hE0 : HasDerivAt (fun z : ℝ => -(z ^ 2) / (4 * t))
        (-(2 * y) / (4 * t)) y := by
      simpa [Function.comp_def] using
        (((hasDerivAt_id' y).pow 2).neg.div_const (4 * t))
    convert hE0 using 1
    field_simp [htime_ne]
    ring
  have hderiv : ∀ y : ℝ,
      deriv (gaussianHeatKernel t) y =
        -(y / (2 * t)) * gaussianHeatKernel t y := by
    intro y
    have hE := hE_spatial y
    have hexp : deriv (fun z : ℝ => Real.exp (-(z ^ 2) / (4 * t))) y =
        Real.exp (-(y ^ 2) / (4 * t)) * (-(y / (2 * t))) := by
      rw [show (fun z : ℝ => Real.exp (-(z ^ 2) / (4 * t))) =
          Real.exp ∘ (fun z : ℝ => -(z ^ 2) / (4 * t)) by rfl]
      simpa [Real.deriv_exp, hE.deriv] using
        (deriv_comp y Real.differentiableAt_exp hE.differentiableAt)
    unfold gaussianHeatKernel
    change deriv (fun z : ℝ => (Real.sqrt (4 * Real.pi * t))⁻¹ *
        Real.exp (-(z ^ 2) / (4 * t))) y = _
    rw [deriv_const_mul_field, hexp]
    ring
  refine ⟨hcont, ?_⟩
  intro x
  refine ⟨hderiv x, ?_, ?_⟩
  · rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rw [show deriv (deriv (gaussianHeatKernel t)) x =
        deriv (fun y : ℝ => -(y / (2 * t)) * gaussianHeatKernel t y) x by
          congr 1
          funext y
          exact hderiv y]
    have hlin : deriv (fun y : ℝ => -(y / (2 * t))) x =
        -(1 / (2 * t)) := by
      rw [show (fun y : ℝ => -(y / (2 * t))) =
          (fun y : ℝ => (-(2 * t)⁻¹) * y) by
            funext z
            field_simp [htime_ne]]
      rw [deriv_const_mul_id]
      field_simp [htime_ne]
    have hq := deriv_fun_mul (x := x)
      (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => -(y / (2 * t))) x)
      (hcont.differentiable (by simp) x)
    rw [hlin, hderiv x] at hq
    rw [hq]
    unfold gaussianHeatHessian
    field_simp [htime_ne]
    ring
  · have hargDiff : DifferentiableAt ℝ (fun s : ℝ => 4 * Real.pi * s) t := by
      fun_prop
    have hsqrtDiff : DifferentiableAt ℝ (fun s : ℝ =>
        Real.sqrt (4 * Real.pi * s)) t :=
      hargDiff.sqrt htime_pos.ne'
    have hsqrtDeriv : deriv (fun s : ℝ => Real.sqrt (4 * Real.pi * s)) t =
        (4 * Real.pi) / (2 * Real.sqrt (4 * Real.pi * t)) := by
      simpa using deriv_sqrt hargDiff htime_pos.ne'
    have hnormDiff : DifferentiableAt ℝ (fun s : ℝ =>
        (Real.sqrt (4 * Real.pi * s))⁻¹) t :=
      hsqrtDiff.inv hsqrt_ne
    have hnormDeriv : deriv (fun s : ℝ =>
        (Real.sqrt (4 * Real.pi * s))⁻¹) t =
        -((4 * Real.pi) / (2 * Real.sqrt (4 * Real.pi * t))) /
          (Real.sqrt (4 * Real.pi * t)) ^ 2 := by
      rw [deriv_fun_inv'' hsqrtDiff hsqrt_ne, hsqrtDeriv]
    have hEtimeDiff : DifferentiableAt ℝ
        (fun s : ℝ => -(x ^ 2) / (4 * s)) t := by
      have hinv : DifferentiableAt ℝ (fun s : ℝ => s⁻¹) t :=
        differentiableAt_inv_iff.mpr htime_ne
      have htmp := hinv.const_mul (-(x ^ 2) / 4)
      exact htmp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by ring))
    have hEtimeDeriv : deriv (fun s : ℝ => -(x ^ 2) / (4 * s)) t =
        x ^ 2 / (4 * t ^ 2) := by
      rw [show (fun s : ℝ => -(x ^ 2) / (4 * s)) =
          (fun s : ℝ => (-(x ^ 2) / 4) * s⁻¹) by
            funext s
            field_simp [htime_ne]]
      rw [deriv_const_mul_field, deriv_inv]
      field_simp [htime_ne]
    have hexpTime : deriv (fun s : ℝ =>
        Real.exp (-(x ^ 2) / (4 * s))) t =
        Real.exp (-(x ^ 2) / (4 * t)) * (x ^ 2 / (4 * t ^ 2)) := by
      rw [show (fun s : ℝ => Real.exp (-(x ^ 2) / (4 * s))) =
          Real.exp ∘ (fun s : ℝ => -(x ^ 2) / (4 * s)) by rfl]
      simpa [Real.deriv_exp, hEtimeDeriv] using
        (deriv_comp t Real.differentiableAt_exp hEtimeDiff)
    unfold gaussianHeatKernel
    change deriv (fun s : ℝ =>
      (Real.sqrt (4 * Real.pi * s))⁻¹ *
        Real.exp (-(x ^ 2) / (4 * s))) t = _
    rw [deriv_fun_mul hnormDiff (by fun_prop :
      DifferentiableAt ℝ (fun s : ℝ => Real.exp (-(x ^ 2) / (4 * s))) t)]
    rw [hnormDeriv, hexpTime]
    unfold gaussianHeatHessian
    unfold gaussianHeatKernel
    rw [Real.sq_sqrt (le_of_lt htime_pos)]
    field_simp [htime_ne, hsqrt_ne]
    ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
