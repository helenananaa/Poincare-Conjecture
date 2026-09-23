import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHessianCancellation
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicWeightedHessian
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** anisotropic holder hessian. -/
theorem anisotropic_holder_hessian 
    (B : E3 ≃L[ℝ] E3) (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E3 →ᵇ ℝ) (L : ℝ), 0 ≤ L →
      (∀ x y, |f x-f y| ≤ L*‖x-y‖^alpha) → ∀ t : ℝ, 0 < t →
      ∀ (x : E3) (i j : Fin 3),
        let H := fun y : E3 => fderiv ℝ (fun z : E3 => fderiv ℝ (anisotropicHeatKernel B t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1);
        Integrable (fun y : E3 => H y*f (x-y)) volume ∧
          |∫ y : E3, H y*f (x-y)| ≤ C*L*t^(alpha/2-1) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hCpos, hmoment⟩ :=
    anisotropic_weighted_hessian B alpha ha ha1
  refine ⟨C, hCpos, ?_⟩
  intro f L hL hHolder t ht x i j
  let H : E3 → ℝ := fun y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (anisotropicHeatKernel B t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
  change Integrable (fun y : E3 => H y * f (x-y)) volume ∧
    |∫ y : E3, H y * f (x-y)| ≤ C * L * t^(alpha/2-1)
  have hcancel := anisotropic_hessian_cancellation B t ht i j
  have hHint : Integrable H volume := by
    simpa [H] using hcancel.1
  have hHmass : (∫ y : E3, H y) = 0 := by
    simpa [H] using hcancel.2
  have hmomentInt : Integrable (fun y : E3 => |H y| * ‖y‖^alpha) volume := by
    simpa [H] using (hmoment t ht i j).1
  have hmomentBound :
      (∫ y : E3, |H y| * ‖y‖^alpha) ≤ C * t^(alpha/2-1) := by
    simpa [H] using (hmoment t ht i j).2
  have hshift_meas : AEStronglyMeasurable (fun y : E3 => f (x-y)) volume :=
    (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hshift_bound : ∀ᵐ y ∂volume, ‖f (x-y)‖ ≤ ‖f‖ :=
    Filter.Eventually.of_forall fun y => f.norm_coe_le_norm (x-y)
  have hactual : Integrable (fun y : E3 => H y * f (x-y)) volume :=
    hHint.mul_bdd hshift_meas hshift_bound
  have hconstant : Integrable (fun y : E3 => H y * f x) volume :=
    hHint.mul_const (f x)
  have hconstant_eval : (∫ y : E3, H y * f x) = 0 := by
    rw [integral_mul_const, hHmass]
    simp
  have hdiff : Integrable
      (fun y : E3 => H y * f (x-y) - H y * f x) volume :=
    hactual.sub hconstant
  have hcenter :
      (∫ y : E3, H y * f (x-y)) =
        ∫ y : E3, (H y * f (x-y) - H y * f x) := by
    calc
      (∫ y : E3, H y * f (x-y)) =
          (∫ y : E3, H y * f (x-y)) - (∫ y : E3, H y * f x) := by
            rw [hconstant_eval]
            ring
      _ = ∫ y : E3, (H y * f (x-y) - H y * f x) :=
        (integral_sub hactual hconstant).symm
  have hscaledMoment : Integrable
      (fun y : E3 => L * (|H y| * ‖y‖^alpha)) volume :=
    hmomentInt.const_mul L
  refine ⟨hactual, ?_⟩
  rw [hcenter]
  calc
    |∫ y : E3, (H y * f (x-y) - H y * f x)| ≤
        ∫ y : E3, |H y * f (x-y) - H y * f x| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y : E3, L * (|H y| * ‖y‖^alpha) := by
      apply integral_mono hdiff.abs hscaledMoment
      intro y
      have hholder := hHolder (x-y) x
      have hdist : ‖(x-y)-x‖ = ‖y‖ := by simp
      rw [hdist] at hholder
      calc
        |H y * f (x-y) - H y * f x| =
            |H y| * |f (x-y) - f x| := by
              rw [← mul_sub, abs_mul]
        _ ≤ |H y| * (L * ‖y‖^alpha) :=
          mul_le_mul_of_nonneg_left hholder (abs_nonneg _)
        _ = L * (|H y| * ‖y‖^alpha) := by ring
    _ = L * (∫ y : E3, |H y| * ‖y‖^alpha) := by
      rw [integral_const_mul]
    _ ≤ L * (C * t^(alpha/2-1)) :=
      mul_le_mul_of_nonneg_left hmomentBound hL
    _ = C * L * t^(alpha/2-1) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
