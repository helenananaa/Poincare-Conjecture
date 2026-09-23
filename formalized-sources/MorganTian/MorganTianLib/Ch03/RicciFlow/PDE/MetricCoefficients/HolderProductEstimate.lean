import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** holder product estimate. -/
theorem holder_product_estimate 
    (f g : E3 →ᵇ ℝ) (alpha Hf Hg : ℝ) (hf0 : 0 ≤ Hf) (hg0 : 0 ≤ Hg)
    (hf : ∀ x y, |f x-f y| ≤ Hf*‖x-y‖^alpha)
    (hg : ∀ x y, |g x-g y| ≤ Hg*‖x-y‖^alpha) :
    ∀ x y, |f x*g x-f y*g y| ≤ (‖f‖*Hg+‖g‖*Hf)*‖x-y‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  intro x y
  have hr : 0 ≤ ‖x - y‖ ^ alpha := by positivity
  have hfx : |f x| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have hgy : |g y| ≤ ‖g‖ := by
    simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm y
  have hsplit : f x * g x - f y * g y =
      f x * (g x - g y) + (f x - f y) * g y := by ring
  calc
    |f x * g x - f y * g y| =
        |f x * (g x - g y) + (f x - f y) * g y| := by rw [hsplit]
    _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add_le _ _
    _ = |f x| * |g x - g y| + |f x - f y| * |g y| := by rw [abs_mul, abs_mul]
    _ ≤ ‖f‖ * (Hg * ‖x - y‖ ^ alpha) +
          (Hf * ‖x - y‖ ^ alpha) * ‖g‖ := by
      apply add_le_add
      · calc
          |f x| * |g x - g y| ≤ ‖f‖ * |g x - g y| :=
            mul_le_mul_of_nonneg_right hfx (abs_nonneg _)
          _ ≤ ‖f‖ * (Hg * ‖x - y‖ ^ alpha) :=
            mul_le_mul_of_nonneg_left (hg x y) (norm_nonneg _)
      · calc
          |f x - f y| * |g y| ≤ (Hf * ‖x - y‖ ^ alpha) * |g y| :=
            mul_le_mul_of_nonneg_right (hf x y) (abs_nonneg _)
          _ ≤ (Hf * ‖x - y‖ ^ alpha) * ‖g‖ :=
            mul_le_mul_of_nonneg_left hgy (mul_nonneg hf0 hr)
    _ = (‖f‖ * Hg + ‖g‖ * Hf) * ‖x - y‖ ^ alpha := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
