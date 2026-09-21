import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Basic
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Semigroup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Equation
open Set MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace MorganTianLib.ParabolicPDE
/-- **Math.** The actual second spatial derivative is integrable and has zero mass. -/
theorem gaussianHeatKernel_hessian_cancellation {t : ℝ} (ht : 0 < t) :
    Integrable (iteratedDeriv 2 (gaussianHeatKernel t)) volume ∧
      (∫ x : ℝ, iteratedDeriv 2 (gaussianHeatKernel t) x) = 0 := by
/- SWARM_PROOF_BEGIN -/
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hcoef : 0 < (1 / (4 * t) : ℝ) := by positivity
  have hbase : Integrable
      (fun x : ℝ => Real.exp (-(1 / (4 * t)) * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq hcoef
  have hquad : Integrable
      (fun x : ℝ => x ^ 2 * Real.exp (-(1 / (4 * t)) * x ^ 2)) volume := by
    convert integrable_rpow_mul_exp_neg_mul_sq hcoef (s := (2 : ℝ)) (by norm_num) using 1 <;>
      simp
  have hcomb : Integrable
      (fun x : ℝ =>
        (Real.sqrt (4 * Real.pi * t))⁻¹ *
          ((1 / (4 * t ^ 2)) * (x ^ 2 * Real.exp (-(1 / (4 * t)) * x ^ 2)) -
            (1 / (2 * t)) * Real.exp (-(1 / (4 * t)) * x ^ 2))) volume := by
    have hinside : Integrable
        (fun x : ℝ =>
          (1 / (4 * t ^ 2)) * (x ^ 2 * Real.exp (-(1 / (4 * t)) * x ^ 2)) -
            (1 / (2 * t)) * Real.exp (-(1 / (4 * t)) * x ^ 2)) volume := by
      exact (hquad.const_mul _).sub (hbase.const_mul _)
    exact hinside.const_mul _
  have hhess : Integrable (iteratedDeriv 2 (gaussianHeatKernel t)) volume := by
    refine hcomb.congr ?_
    filter_upwards [] with x
    have hformula := (gaussianHeatKernel_derivatives ht).2 x |>.2.1
    rw [hformula]
    unfold gaussianHeatHessian gaussianHeatKernel
    field_simp [ht0]
  refine ⟨hhess, ?_⟩
  have hderiv := (gaussianHeatKernel_derivatives ht).2
  apply integral_eq_zero_of_hasDerivAt_of_integrable
    (f := deriv (gaussianHeatKernel t))
    (f' := iteratedDeriv 2 (gaussianHeatKernel t))
  · intro x
    rw [show iteratedDeriv 2 (gaussianHeatKernel t) x =
        deriv (deriv (gaussianHeatKernel t)) x by
          rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
            iteratedDeriv_one]]
    rw [show deriv (gaussianHeatKernel t) =
        fun y : ℝ => -(y / (2 * t)) * gaussianHeatKernel t y by
          funext y
          exact (hderiv y).1]
    have hgauss : DifferentiableAt ℝ (gaussianHeatKernel t) x :=
      (gaussianHeatKernel_derivatives ht).1.differentiable (by simp) x
    have hlin : DifferentiableAt ℝ (fun y : ℝ => -(y / (2 * t))) x := by
      fun_prop
    exact (hlin.mul hgauss).hasDerivAt
  · exact hhess
  · have hfirst : Integrable (deriv (gaussianHeatKernel t)) volume := by
      have hlin : Integrable
          (fun x : ℝ => x * Real.exp (-(1 / (4 * t)) * x ^ 2)) volume :=
        integrable_mul_exp_neg_mul_sq hcoef
      have hscaled : Integrable
          (fun x : ℝ => -(x / (2 * t)) *
            ((Real.sqrt (4 * Real.pi * t))⁻¹ *
              Real.exp (-(1 / (4 * t)) * x ^ 2))) volume := by
        have hscaled0 : Integrable
            (fun x : ℝ => (Real.sqrt (4 * Real.pi * t))⁻¹ *
              (-(1 / (2 * t)) *
                (x * Real.exp (-(1 / (4 * t)) * x ^ 2)))) volume :=
          (hlin.const_mul _).const_mul _
        refine hscaled0.congr ?_
        filter_upwards [] with x
        ring
      refine hscaled.congr ?_
      filter_upwards [] with x
      rw [(hderiv x).1]
      unfold gaussianHeatKernel
      congr 1
      field_simp [ht0]
    exact hfirst
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
