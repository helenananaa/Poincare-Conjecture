import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianEstimate
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideHessianUnweighted
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatTimeDerivativeL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalInitialTrace
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ShiftedDerivativeDominator
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- An actual integral error estimate when freezing a Holder coefficient. -/
theorem heat_hessian_coefficient_commutator (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : E3 → ℝ), Continuous a →
      ∀ (L : ℝ), 0 ≤ L → (∀ x y : E3, |a x-a y| ≤ L*‖x-y‖^alpha) →
      ∀ (f : E3 →ᵇ ℝ) (t : ℝ), 0 < t → ∀ (x : E3) (i j : Fin 3),
        Integrable (fun y : E3 => (a x-a (x-y))*
          fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*f (x-y)) volume ∧
        |∫ y : E3, (a x-a (x-y))*fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*f (x-y)| ≤
            C*L*‖f‖*t^(alpha/2-1) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    euclideanHeatKernel_three_weighted_hessian_recursive alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro a ha_cont L hL hholder f t ht x i j
  obtain ⟨hweight, hweight_bound⟩ := hbound t ht i j
  let H : E3 → ℝ := fun y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
  have hH_eq (y : E3) : H y =
      (y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) *
        euclideanHeatKernel 3 t y := by
    exact euclideanHeatKernel_three_hessian_formula ht y i j
  have hH_cont : Continuous H := by
    rw [show H = (fun y : E3 =>
        (y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) *
          euclideanHeatKernel 3 t y) by
      funext y
      exact hH_eq y]
    have hKcont : Continuous (fun y : E3 => euclideanHeatKernel 3 t y) := by
      unfold euclideanHeatKernel
      exact (contDiff_prod (fun k _ =>
        (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
    have hcoef : Continuous (fun y : E3 =>
        y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) := by
      fun_prop
    exact hcoef.mul hKcont
  let error : E3 → ℝ := fun y =>
    (a x - a (x - y)) * H y * f (x - y)
  have herror_cont : Continuous error := by
    dsimp [error]
    exact (continuous_const.sub
      (ha_cont.comp (continuous_const.sub continuous_id))).mul hH_cont |>.mul
      (f.continuous.comp (continuous_const.sub continuous_id))
  have herror_meas : Measurable error := herror_cont.measurable
  let majorant : E3 → ℝ := fun y =>
    L * ‖f‖ * (|H y| * ‖y‖ ^ alpha)
  have hmajorant_int : Integrable majorant volume := by
    dsimp [majorant]
    exact hweight.const_mul _
  have herror_bound : ∀ y : E3, ‖error y‖ ≤ majorant y := by
    intro y
    have hy : x - (x - y) = y := by
      abel
    have hcoef : |a x - a (x - y)| ≤ L * ‖y‖ ^ alpha := by
      simpa [hy] using hholder x (x - y)
    have hf : |f (x - y)| ≤ ‖f‖ := by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (x - y)
    dsimp [error, majorant]
    calc
      ‖(a x - a (x - y)) * H y * f (x - y)‖ =
          |a x - a (x - y)| * |H y| * |f (x - y)| := by
            simp only [norm_mul, Real.norm_eq_abs]
      _ ≤ (L * ‖y‖ ^ alpha) * |H y| * ‖f‖ := by
        calc
          |a x - a (x - y)| * |H y| * |f (x - y)| ≤
              (L * ‖y‖ ^ alpha) * |H y| * |f (x - y)| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)) (abs_nonneg _)
          _ ≤ (L * ‖y‖ ^ alpha) * |H y| * ‖f‖ := by
            exact mul_le_mul_of_nonneg_left hf
              (mul_nonneg (mul_nonneg hL (Real.rpow_nonneg (norm_nonneg y) _))
                (abs_nonneg _))
      _ = L * ‖f‖ * (|H y| * ‖y‖ ^ alpha) := by ring
  have herror_int : Integrable error volume := by
    refine hmajorant_int.mono' herror_meas.aestronglyMeasurable ?_
    filter_upwards [] with y
    exact herror_bound y
  refine ⟨herror_int, ?_⟩
  calc
    |∫ y : E3, (a x - a (x - y)) * H y * f (x - y)| =
        ‖∫ y : E3, error y‖ := by rfl
    _ ≤ ∫ y : E3, majorant y :=
      norm_integral_le_of_norm_le hmajorant_int
        (Eventually.of_forall herror_bound)
    _ = L * ‖f‖ * (∫ y : E3, |H y| * ‖y‖ ^ alpha) := by
      dsimp [majorant]
      rw [integral_const_mul]
    _ ≤ L * ‖f‖ * (C * t ^ (alpha / 2 - 1)) := by
      exact mul_le_mul_of_nonneg_left hweight_bound
        (mul_nonneg hL (norm_nonneg _))
    _ = C * L * ‖f‖ * t ^ (alpha / 2 - 1) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
