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
/-- A single Gaussian controls every shift and time in a compact positive-time set. -/
theorem euclideanHeatKernel_compact_time_space_bound (a b R : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (x y : E3), t ∈ Icc a b → ‖x‖ ≤ R →
      euclideanHeatKernel 3 t (x-y) ≤ C*euclideanHeatKernel 3 (2*b) y :=
/- SWARM_PROOF_BEGIN -/
by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let C : ℝ :=
    ((Real.sqrt (4 * Real.pi * a))⁻¹ ^ (3 : ℕ) /
      ((Real.sqrt (4 * Real.pi * (2 * b)))⁻¹ ^ (3 : ℕ))) *
      Real.exp (R ^ 2 / (4 * b))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    have haa : 0 < 4 * Real.pi * a := by positivity
    have hbb : 0 < 4 * Real.pi * (2 * b) := by positivity
    have hsa : 0 < Real.sqrt (4 * Real.pi * a) := Real.sqrt_pos.2 haa
    have hsb : 0 < Real.sqrt (4 * Real.pi * (2 * b)) := Real.sqrt_pos.2 hbb
    positivity
  · intro t x y ht hxy
    rcases ht with ⟨hat, htb⟩
    have hta : 0 < t := lt_of_lt_of_le ha hat
    have h4a : 0 < 4 * Real.pi * a := by positivity
    have h4t : 0 < 4 * Real.pi * t := by positivity
    have h4b2 : 0 < 4 * Real.pi * (2 * b) := by positivity
    have hnorm : ‖y‖ ≤ R + ‖x - y‖ := by
      calc
        ‖y‖ = ‖x - (x - y)‖ := by congr 1 <;> abel
        _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
        _ ≤ R + ‖x - y‖ := by
          simpa [add_comm] using add_le_add_left hxy ‖x - y‖
    have hnormsq : ‖y‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * R ^ 2 := by
      have hp : 0 ≤ (R + ‖x - y‖ + ‖y‖) *
          (R + ‖x - y‖ - ‖y‖) := by
        apply mul_nonneg
        · positivity
        · linarith
      nlinarith [sq_nonneg (R - ‖x - y‖), hp]
    have hAt :
        (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) ≤
          (Real.sqrt (4 * Real.pi * a))⁻¹ ^ (3 : ℕ) := by
      have harg : 4 * Real.pi * a ≤ 4 * Real.pi * t := by
        nlinarith [Real.pi_pos]
      have hsqrt : Real.sqrt (4 * Real.pi * a) ≤
          Real.sqrt (4 * Real.pi * t) := Real.sqrt_le_sqrt harg
      have hinv : (Real.sqrt (4 * Real.pi * t))⁻¹ ≤
          (Real.sqrt (4 * Real.pi * a))⁻¹ := by
        exact (inv_le_inv₀ (Real.sqrt_pos.2 h4t) (Real.sqrt_pos.2 h4a)).2 hsqrt
      exact pow_le_pow_left₀ (by positivity) hinv 3
    have htime : ‖x - y‖ ^ 2 / (4 * b) ≤ ‖x - y‖ ^ 2 / (4 * t) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (by nlinarith)
    have hydiv : ‖y‖ ^ 2 / (8 * b) ≤
        ‖x - y‖ ^ 2 / (4 * b) + R ^ 2 / (4 * b) := by
      calc
        ‖y‖ ^ 2 / (8 * b) ≤
            (2 * ‖x - y‖ ^ 2 + 2 * R ^ 2) / (8 * b) :=
          div_le_div_of_nonneg_right hnormsq (by positivity)
        _ = ‖x - y‖ ^ 2 / (4 * b) + R ^ 2 / (4 * b) := by
          field_simp
          ring
    have hexp :
        Real.exp (-‖x - y‖ ^ 2 / (4 * t)) ≤
          Real.exp (R ^ 2 / (4 * b)) *
            Real.exp (-‖y‖ ^ 2 / (8 * b)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      calc
        -‖x - y‖ ^ 2 / (4 * t) ≤ -‖x - y‖ ^ 2 / (4 * b) := by
          have h := neg_le_neg htime
          simpa only [neg_div] using h
        _ ≤ R ^ 2 / (4 * b) - ‖y‖ ^ 2 / (8 * b) := by
          calc
            -‖x - y‖ ^ 2 / (4 * b) =
                -(‖x - y‖ ^ 2 / (4 * b)) := by ring
            _ ≤ -(‖y‖ ^ 2 / (8 * b)) + R ^ 2 / (4 * b) := by
              linarith
            _ = R ^ 2 / (4 * b) - ‖y‖ ^ 2 / (8 * b) := by ring
        _ = R ^ 2 / (4 * b) + -‖y‖ ^ 2 / (8 * b) := by ring
    have hA2 : 0 < (Real.sqrt (4 * Real.pi * (2 * b)))⁻¹ ^ (3 : ℕ) := by
      positivity
    have hcoef :
        (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
            Real.exp (R ^ 2 / (4 * b)) ≤
          C * (Real.sqrt (4 * Real.pi * (2 * b)))⁻¹ ^ (3 : ℕ) := by
      have hmul :
          (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
              Real.exp (R ^ 2 / (4 * b)) ≤
            (Real.sqrt (4 * Real.pi * a))⁻¹ ^ (3 : ℕ) *
              Real.exp (R ^ 2 / (4 * b)) :=
        mul_le_mul_of_nonneg_right hAt (Real.exp_pos _).le
      calc
        (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
              Real.exp (R ^ 2 / (4 * b)) ≤
            (Real.sqrt (4 * Real.pi * a))⁻¹ ^ (3 : ℕ) *
              Real.exp (R ^ 2 / (4 * b)) := hmul
        _ = C * (Real.sqrt (4 * Real.pi * (2 * b)))⁻¹ ^ (3 : ℕ) := by
          dsimp [C]
          field_simp [ne_of_gt hA2]
    rw [euclideanHeatKernel_three_norm_form, euclideanHeatKernel_three_norm_form]
    calc
      (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
          Real.exp (-‖x - y‖ ^ 2 / (4 * t)) ≤
          (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
            (Real.exp (R ^ 2 / (4 * b)) *
              Real.exp (-‖y‖ ^ 2 / (8 * b))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) *
            Real.exp (R ^ 2 / (4 * b))) *
          Real.exp (-‖y‖ ^ 2 / (8 * b)) := by ring
      _ ≤ (C * (Real.sqrt (4 * Real.pi * (2 * b)))⁻¹ ^ (3 : ℕ)) *
          Real.exp (-‖y‖ ^ 2 / (8 * b)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
      _ = C * ((Real.sqrt (4 * Real.pi * (2 * b)))⁻¹ ^ (3 : ℕ) *
          Real.exp (-‖y‖ ^ 2 / (4 * (2 * b)))) := by
        have heq : (-‖y‖ ^ 2 / (8 * b) : ℝ) =
            -‖y‖ ^ 2 / (4 * (2 * b)) := by
          field_simp
          ring
        rw [heq]
        ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
