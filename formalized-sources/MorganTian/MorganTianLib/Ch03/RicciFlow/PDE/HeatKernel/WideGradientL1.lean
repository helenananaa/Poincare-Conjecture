import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHolderControl
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- First-order spatial smoothing has a uniform L1 gradient bound. -/
theorem euclideanHeatKernel_three_gradient_L1 :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ i : Fin 3,
      Integrable (fun y : E3 => fderiv ℝ (euclideanHeatKernel 3 t) y
        (EuclideanSpace.single i 1)) volume ∧
      (∫ y : E3, |fderiv ℝ (euclideanHeatKernel 3 t) y (EuclideanSpace.single i 1)|)
        ≤ C/Real.sqrt t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C₁, hC₁, hmoment⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (1 : ℝ) (by norm_num)
  let C : ℝ := C₁ / 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht i
  let G : E3 → ℝ := fun y =>
    (1 / (2 * t)) * (euclideanHeatKernel 3 t y * ‖y‖)
  have hG : Integrable G volume := by
    dsimp [G]
    convert (hmoment t ht).1.const_mul (1 / (2 * t)) using 1 <;>
      simp [Real.rpow_one]
  have hKcont : Continuous (fun y : E3 => euclideanHeatKernel 3 t y) := by
    unfold euclideanHeatKernel
    exact (contDiff_prod (fun k _ =>
      (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
  have htarget_meas : Measurable
      (fun y : E3 =>
        |fderiv ℝ (euclideanHeatKernel 3 t) y
          (EuclideanSpace.single i 1)|) := by
    have hformula :
        (fun y : E3 =>
          |fderiv ℝ (euclideanHeatKernel 3 t) y
            (EuclideanSpace.single i 1)|) =
        (fun y : E3 =>
          |-(y i / (2 * t)) * euclideanHeatKernel 3 t y|) := by
      funext y
      rw [euclideanHeatKernel_three_gradient_formula ht y i]
    rw [hformula]
    have hcoef : Continuous (fun y : E3 => -(y i / (2 * t))) := by
      fun_prop
    exact (hcoef.mul hKcont).abs.measurable
  have hderiv_meas : Measurable
      (fun y : E3 => fderiv ℝ (euclideanHeatKernel 3 t) y
        (EuclideanSpace.single i 1)) := by
    have hformula :
        (fun y : E3 => fderiv ℝ (euclideanHeatKernel 3 t) y
          (EuclideanSpace.single i 1)) =
        (fun y : E3 => -(y i / (2 * t)) * euclideanHeatKernel 3 t y) := by
      funext y
      rw [euclideanHeatKernel_three_gradient_formula ht y i]
    rw [hformula]
    have hcoef : Continuous (fun y : E3 => -(y i / (2 * t))) := by
      fun_prop
    exact (hcoef.mul hKcont).measurable
  have hpoint (y : E3) :
      |fderiv ℝ (euclideanHeatKernel 3 t) y
        (EuclideanSpace.single i 1)| ≤ G y := by
    rw [euclideanHeatKernel_three_gradient_formula ht y i, abs_mul, abs_neg,
      abs_div, abs_of_pos (by positivity : 0 < 2 * t), abs_of_nonneg
        (euclideanHeatKernel_pos 3 ht y).le]
    have hy : |y i| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y i)
    have hK : 0 ≤ euclideanHeatKernel 3 t y :=
      (euclideanHeatKernel_pos 3 ht y).le
    have hcoef : 0 ≤ 1 / (2 * t) := by positivity
    calc
      |y i| / (2 * t) * euclideanHeatKernel 3 t y =
          (1 / (2 * t)) * (|y i| * euclideanHeatKernel 3 t y) := by ring
      _ ≤ (1 / (2 * t)) * (‖y‖ * euclideanHeatKernel 3 t y) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hy hK) hcoef
      _ = G y := by
        dsimp [G]
        ring
  have htarget : Integrable
      (fun y : E3 =>
        |fderiv ℝ (euclideanHeatKernel 3 t) y
          (EuclideanSpace.single i 1)|) volume := by
    refine hG.mono' htarget_meas.aestronglyMeasurable ?_
    filter_upwards [] with y
    simpa [Real.norm_eq_abs, abs_nonneg] using hpoint y
  have htarget_deriv : Integrable
      (fun y : E3 => fderiv ℝ (euclideanHeatKernel 3 t) y
        (EuclideanSpace.single i 1)) volume := by
    apply (integrable_norm_iff hderiv_meas.aestronglyMeasurable).mp
    simpa [Real.norm_eq_abs] using htarget
  have hG_int : (∫ y : E3, G y) =
      (1 / (2 * t)) *
        (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖) := by
    dsimp [G]
    rw [integral_const_mul]
  have hle :
      (∫ y : E3,
        |fderiv ℝ (euclideanHeatKernel 3 t) y
          (EuclideanSpace.single i 1)|) ≤ ∫ y : E3, G y :=
    integral_mono htarget hG hpoint
  rw [hG_int] at hle
  have htime :
      (1 / (2 * t)) * (C₁ * t ^ ((1 : ℝ) / 2)) =
        (C₁ / 2) / Real.sqrt t := by
    rw [← Real.sqrt_eq_rpow]
    field_simp [ht.ne', Real.sqrt_ne_zero'.2 ht]
    rw [Real.sq_sqrt ht.le]
  have hmoment_norm :
      (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖) ≤
        C₁ * t ^ ((1 : ℝ) / 2) := by
    simpa [Real.rpow_one] using (hmoment t ht).2
  dsimp [C]
  refine ⟨htarget_deriv, ?_⟩
  calc
    (∫ y : E3,
        |fderiv ℝ (euclideanHeatKernel 3 t) y
          (EuclideanSpace.single i 1)|) ≤
        (1 / (2 * t)) * (C₁ * t ^ ((1 : ℝ) / 2)) := by
      exact hle.trans (mul_le_mul_of_nonneg_left hmoment_norm (by positivity))
    _ = (C₁ / 2) / Real.sqrt t := htime
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
