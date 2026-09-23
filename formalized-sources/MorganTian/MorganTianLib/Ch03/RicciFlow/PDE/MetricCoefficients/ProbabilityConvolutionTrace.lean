import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** probability convolution trace error. -/
theorem probability_convolution_trace_error 
    (k : E3 → ℝ) (hk : Integrable k volume) (hpos : ∀ x, 0 ≤ k x)
    (hmass : (∫ x : E3, k x) = 1) (alpha H : ℝ) (hH : 0 ≤ H)
    (hmoment : Integrable (fun y : E3 => k y*‖y‖^alpha) volume)
    (f : E3 →ᵇ ℝ) (hf : ∀ x y, |f x-f y| ≤ H*‖x-y‖^alpha) :
    ∀ x, |(∫ y : E3, k y*f (x-y))-f x| ≤ H*(∫ y : E3, k y*‖y‖^alpha) :=
/- SWARM_PROOF_BEGIN -/
by
  intro x
  have hshift_meas : AEStronglyMeasurable (fun y : E3 => f (x - y)) volume :=
    (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hshift_bound : ∀ᵐ y ∂volume, ‖f (x - y)‖ ≤ ‖f‖ :=
    Filter.Eventually.of_forall fun y => f.norm_coe_le_norm (x - y)
  have hconv : Integrable (fun y : E3 => k y * f (x - y)) volume :=
    hk.mul_bdd hshift_meas hshift_bound
  have hconstant : Integrable (fun y : E3 => k y * f x) volume :=
    hk.mul_const (f x)
  have hconstant_eval : (∫ y : E3, k y * f x) = f x := by
    rw [integral_mul_const]
    simp [hmass]
  rw [← hconstant_eval, ← integral_sub hconv hconstant]
  have hscaled_moment :
      Integrable (fun y : E3 => H * (k y * ‖y‖ ^ alpha)) volume :=
    hmoment.const_mul H
  have hdiff :
      Integrable (fun y : E3 => k y * f (x - y) - k y * f x) volume :=
    hconv.sub hconstant
  calc
    |∫ y : E3, (k y * f (x - y) - k y * f x)| ≤
        ∫ y : E3, |k y * f (x - y) - k y * f x| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y : E3, H * (k y * ‖y‖ ^ alpha) := by
      apply integral_mono hdiff.abs hscaled_moment
      intro y
      have hpoint := hf (x - y) x
      have hdist : ‖(x - y) - x‖ = ‖y‖ := by simp
      rw [hdist] at hpoint
      calc
        |k y * f (x - y) - k y * f x|
            = k y * |f (x - y) - f x| := by
                rw [← mul_sub, abs_mul, abs_of_nonneg (hpos y)]
        _ ≤ k y * (H * ‖y‖ ^ alpha) :=
          mul_le_mul_of_nonneg_left hpoint (hpos y)
        _ = H * (k y * ‖y‖ ^ alpha) := by ring
    _ = H * (∫ y : E3, k y * ‖y‖ ^ alpha) := by
      rw [integral_const_mul]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
