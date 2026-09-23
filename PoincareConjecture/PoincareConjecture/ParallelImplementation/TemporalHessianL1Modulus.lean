import PoincareConjecture.ParallelImplementation.TemporalHessianSmallL1
import PoincareConjecture.ParallelImplementation.TemporalHessianCoarse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.TemporalHessianL1Modulus
open MorganTianLib.MetricCoefficient
open Set MeasureTheory
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** The actual weighted Hessian time modulus at every positive time scale. -/
theorem heatHessian_time_difference_L1_modulus
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t h : ℝ, 0 < t → 0 < h → ∀ i j : Fin 3,
      Integrable (fun y : E3 =>
        |heatHessian3 (t+h) i j y - heatHessian3 t i j y| * ‖y‖^alpha) volume ∧
      (∫ y : E3, |heatHessian3 (t+h) i j y - heatHessian3 t i j y| * ‖y‖^alpha) ≤
        C * min (t^(alpha/2-1)) (h*t^(alpha/2-2)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨Cs, hCs, hsmall⟩ :=
    PoincareConjecture.ParallelImplementation.TemporalHessianSmallL1.heatHessian_time_difference_small_L1
      alpha ha ha1
  obtain ⟨Cc, hCc, hcoarse⟩ :=
    PoincareConjecture.ParallelImplementation.TemporalHessianCoarse.heatHessian_time_difference_coarse
      alpha ha ha1
  let C := max Cs Cc
  have hC : 0 < C := lt_of_lt_of_le hCs (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro t h ht hh i j
  obtain ⟨hI, hBcoarse⟩ := hcoarse t h ht (le_of_lt hh) i j
  let beta : ℝ := alpha / 2 - 2
  have hbeta : beta + 1 = alpha / 2 - 1 := by
    dsimp [beta]
    ring
  have hpow : 0 < t ^ beta := Real.rpow_pos_of_pos ht beta
  have hpow_nonneg : 0 ≤ t ^ beta := le_of_lt hpow
  by_cases hle : h ≤ t
  · obtain hBsmall := hsmall t h ht (le_of_lt hh) hle i j
    have hcompare : h * t ^ beta ≤ t ^ (alpha / 2 - 1) := by
      calc
        h * t ^ beta ≤ t * t ^ beta := mul_le_mul_of_nonneg_right hle hpow_nonneg
        _ = t ^ (beta + 1) := by rw [Real.rpow_add ht, Real.rpow_one]; ring
        _ = t ^ (alpha / 2 - 1) := by rw [hbeta]
    have hmin : min (t ^ (alpha / 2 - 1)) (h * t ^ beta) = h * t ^ beta :=
      min_eq_right hcompare
    refine ⟨hI, ?_⟩
    calc
      (∫ y : E3, |heatHessian3 (t + h) i j y - heatHessian3 t i j y| * ‖y‖ ^ alpha) ≤
          Cs * h * t ^ beta := by simpa [beta, mul_assoc] using hBsmall
      _ ≤ C * (h * t ^ beta) := by
        dsimp [C]
        calc
          Cs * h * t ^ beta = Cs * (h * t ^ beta) := by ring
          _ ≤ max Cs Cc * (h * t ^ beta) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (le_of_lt hh) hpow_nonneg)
          _ = max Cs Cc * (h * t ^ beta) := rfl
      _ = C * min (t ^ (alpha / 2 - 1)) (h * t ^ beta) := by
        simpa [beta] using congrArg (fun x : ℝ => C * x) hmin.symm
  · have hle : t ≤ h := le_of_not_ge hle
    have hcompare : t ^ (alpha / 2 - 1) ≤ h * t ^ beta := by
      calc
        t ^ (alpha / 2 - 1) = t ^ (beta + 1) := by rw [hbeta]
        _ = t ^ beta * t := by rw [Real.rpow_add ht, Real.rpow_one]
        _ ≤ h * t ^ beta := by
          calc
            t ^ beta * t = t * t ^ beta := by ring
            _ ≤ h * t ^ beta := mul_le_mul_of_nonneg_right hle hpow_nonneg
    have hmin : min (t ^ (alpha / 2 - 1)) (h * t ^ beta) = t ^ (alpha / 2 - 1) :=
      min_eq_left hcompare
    refine ⟨hI, ?_⟩
    calc
      (∫ y : E3, |heatHessian3 (t + h) i j y - heatHessian3 t i j y| * ‖y‖ ^ alpha) ≤
          Cc * t ^ (alpha / 2 - 1) := hBcoarse
      _ ≤ C * t ^ (alpha / 2 - 1) := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)
      _ = C * min (t ^ (alpha / 2 - 1)) (h * t ^ beta) := by
        simpa [beta] using congrArg (fun x : ℝ => C * x) hmin.symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.TemporalHessianL1Modulus
