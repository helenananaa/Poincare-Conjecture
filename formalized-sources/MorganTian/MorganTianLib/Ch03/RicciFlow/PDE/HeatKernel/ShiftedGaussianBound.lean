import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideHessianUnweighted
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Uniform shifted-Gaussian comparison on a compact spatial parameter ball. -/
theorem euclideanHeatKernel_three_shifted_bound (t R : ℝ) (ht : 0 < t) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : E3, ‖x‖ ≤ R →
      euclideanHeatKernel 3 t (x-y) ≤ C*euclideanHeatKernel 3 (2*t) y :=
/- SWARM_PROOF_BEGIN -/
by
  let C : ℝ :=
    ((Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) /
      ((Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ ^ (3 : ℕ))) *
      Real.exp (R ^ 2 / (4 * t))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    have ht0 : 0 < 4 * Real.pi * t := by positivity
    have ht20 : 0 < 4 * Real.pi * (2 * t) := by positivity
    have hst : 0 < Real.sqrt (4 * Real.pi * t) := Real.sqrt_pos.2 ht0
    have hst2 : 0 < Real.sqrt (4 * Real.pi * (2 * t)) := Real.sqrt_pos.2 ht20
    positivity
  · intro x y hxy
    rw [euclideanHeatKernel_three_norm_form, euclideanHeatKernel_three_norm_form]
    have hy : ‖y‖ ≤ R + ‖x - y‖ := by
      calc
        ‖y‖ = ‖x - (x - y)‖ := by congr 1 <;> abel
        _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
        _ ≤ R + ‖x - y‖ := add_le_add_left hxy _
    have hsq : ‖y‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * R ^ 2 := by
      have hp : 0 ≤ (R + ‖x - y‖ + ‖y‖) * (R + ‖x - y‖ - ‖y‖) := by
        apply mul_nonneg
        · nlinarith [norm_nonneg y, norm_nonneg (x - y)]
        · nlinarith
      nlinarith [sq_nonneg (R - ‖x - y‖), hp]
    have hexp :
        Real.exp (-‖x - y‖ ^ 2 / (4 * t)) ≤
          Real.exp (R ^ 2 / (4 * t)) * Real.exp (-‖y‖ ^ 2 / (8 * t)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have ht' : 0 < 8 * t := by positivity
      field_simp
      nlinarith
    have hpos : 0 ≤ Real.exp (-‖y‖ ^ 2 / (8 * t)) := (Real.exp_pos _).le
    have hnorm :
        (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
            Real.exp (R ^ 2 / (4 * t)) ≤
          C * ((Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ ^ (3 : ℕ)) := by
      dsimp [C]
      have ht0 : 0 < 4 * Real.pi * t := by positivity
      have ht20 : 0 < 4 * Real.pi * (2 * t) := by positivity
      have hst : 0 < Real.sqrt (4 * Real.pi * t) := Real.sqrt_pos.2 ht0
      have hst2 : 0 < Real.sqrt (4 * Real.pi * (2 * t)) := Real.sqrt_pos.2 ht20
      have he1 : 1 ≤ Real.exp (R ^ 2 / (4 * t)) :=
        Real.one_le_exp (by positivity)
      field_simp
      nlinarith
    calc
      (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
          Real.exp (-‖x - y‖ ^ 2 / (4 * t)) ≤
          (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
            (Real.exp (R ^ 2 / (4 * t)) *
              Real.exp (-‖y‖ ^ 2 / (8 * t))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ C * ((Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ ^ (3 : ℕ)) *
          Real.exp (-‖y‖ ^ 2 / (8 * t)) := by
        calc
          (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
              (Real.exp (R ^ 2 / (4 * t)) *
                Real.exp (-‖y‖ ^ 2 / (8 * t))) =
              ((Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
                Real.exp (R ^ 2 / (4 * t))) *
                Real.exp (-‖y‖ ^ 2 / (8 * t)) := by ring
          _ ≤ (C * ((Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ ^ (3 : ℕ))) *
              Real.exp (-‖y‖ ^ 2 / (8 * t)) :=
            mul_le_mul_of_nonneg_right hnorm hpos
      _ = C * ((Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ ^ (3 : ℕ)) *
          Real.exp (-‖y‖ ^ 2 / (4 * (2 * t))) := by
        have heq : (-‖y‖ ^ 2 / (8 * t) : ℝ) =
            -‖y‖ ^ 2 / (4 * (2 * t)) := by
          field_simp
          ring
        rw [heq]
      _ = C * (((Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ ^ (3 : ℕ)) *
          Real.exp (-‖y‖ ^ 2 / (4 * (2 * t)))) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
