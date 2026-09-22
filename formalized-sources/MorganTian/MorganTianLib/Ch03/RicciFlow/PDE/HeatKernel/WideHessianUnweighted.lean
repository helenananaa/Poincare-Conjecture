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
/-- A common L1 Hessian bound for all coordinate entries and all positive times. -/
theorem euclideanHeatKernel_three_hessian_L1 :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ i j : Fin 3,
      Integrable (fun y : E3 => fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)) volume ∧
      (∫ y : E3, |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)|) ≤ C/t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C2, hC2, hmoment2⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (2 : ℝ) (by norm_num)
  obtain ⟨C0, hC0, hmoment0⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (0 : ℝ) (by norm_num)
  let C : ℝ := C2 / 4 + C0 / 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht i j
  let F : E3 → ℝ := fun y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
  have hF : Integrable F volume := by
    simpa [F] using (euclideanHeatKernel_three_hessian_cancellation ht i j).1
  let G : E3 → ℝ := fun y =>
    (1 / (4 * t ^ 2)) * (euclideanHeatKernel 3 t y * ‖y‖ ^ (2 : ℕ)) +
      (1 / (2 * t)) * euclideanHeatKernel 3 t y
  have h2 : Integrable
      (fun y : E3 => euclideanHeatKernel 3 t y * ‖y‖ ^ (2 : ℕ)) volume := by
    convert (hmoment2 t ht).1 using 1 <;> norm_num [Real.rpow_two]
  have h0 : Integrable (fun y : E3 => euclideanHeatKernel 3 t y) volume := by
    simpa using (hmoment0 t ht).1
  have hG : Integrable G volume := by
    dsimp [G]
    exact (h2.const_mul _).add (h0.const_mul _)
  have hFformula (y : E3) :
      F y = (y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) *
        euclideanHeatKernel 3 t y := by
    exact euclideanHeatKernel_three_hessian_formula ht y i j
  have hpoint (y : E3) : ‖F y‖ ≤ G y := by
    rw [hFformula y, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (euclideanHeatKernel_pos 3 ht y).le]
    have hyi : |y i| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y i)
    have hyj : |y j| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y j)
    have hprod : |y i * y j| ≤ ‖y‖ ^ (2 : ℕ) := by
      rw [abs_mul]
      exact (mul_le_mul hyi hyj (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)
    have hden : 0 < 4 * t ^ 2 := by positivity
    have hdiag : |(if i = j then 1 / (2 * t) else 0)| ≤ 1 / (2 * t) := by
      by_cases hij : i = j
      · rw [if_pos hij, abs_of_pos (by positivity : 0 < (1 : ℝ) / (2 * t))]
      · rw [if_neg hij, abs_zero]
        positivity
    have hcoef :
        |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| ≤
          ‖y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t) := by
      calc
        |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| ≤
            |y i * y j / (4 * t ^ 2)| +
              |(if i = j then 1 / (2 * t) else 0)| := by
          simpa [abs_neg] using
            (abs_sub_le (y i * y j / (4 * t ^ 2)) (0 : ℝ)
              (if i = j then 1 / (2 * t) else 0))
        _ = |y i * y j| / (4 * t ^ 2) +
              |(if i = j then 1 / (2 * t) else 0)| := by
          rw [abs_div, abs_of_pos hden]
        _ ≤ ‖y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t) := by
          exact add_le_add (div_le_div_of_nonneg_right hprod hden.le) hdiag
    have hmul :
        |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| *
            euclideanHeatKernel 3 t y ≤
          (‖y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t)) *
            euclideanHeatKernel 3 t y :=
      mul_le_mul_of_nonneg_right hcoef (euclideanHeatKernel_pos 3 ht y).le
    calc
      |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| *
          euclideanHeatKernel 3 t y ≤
          (‖y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t)) *
            euclideanHeatKernel 3 t y := hmul
      _ = G y := by
        dsimp [G]
        ring
  have habsF : Integrable (fun y : E3 => |F y|) volume := by
    simpa [Real.norm_eq_abs] using hF.norm
  have hG_int : (∫ y : E3, G y) =
      (1 / (4 * t ^ 2)) *
          (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖ ^ (2 : ℕ)) +
        (1 / (2 * t)) * (∫ y : E3, euclideanHeatKernel 3 t y) := by
    dsimp [G]
    rw [integral_add (h2.const_mul _) (h0.const_mul _),
      integral_const_mul, integral_const_mul]
  have hmoment2' :
      (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖ ^ (2 : ℕ)) ≤ C2 * t := by
    convert (hmoment2 t ht).2 using 1 <;> norm_num [Real.rpow_two]
  have hmoment0' : (∫ y : E3, euclideanHeatKernel 3 t y) ≤ C0 := by
    convert (hmoment0 t ht).2 using 1 <;> norm_num
  refine ⟨?_, ?_⟩
  · simpa [F] using hF
  · have hle : (∫ y : E3, |F y|) ≤ ∫ y : E3, G y :=
      integral_mono habsF hG (fun y => by
        simpa [Real.norm_eq_abs] using hpoint y)
    rw [hG_int] at hle
    calc
      (∫ y : E3, |F y|) ≤
          (1 / (4 * t ^ 2)) * (C2 * t) +
            (1 / (2 * t)) * C0 := by
        exact hle.trans (add_le_add
          (mul_le_mul_of_nonneg_left hmoment2' (by positivity))
          (mul_le_mul_of_nonneg_left hmoment0' (by positivity)))
      _ = C / t := by
        dsimp [C]
        field_simp [ht.ne']
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
