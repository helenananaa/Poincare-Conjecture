import MorganTianLib.Ch02.SurgeryCap.GlobalCapGeometry
import Mathlib
open Riemannian
open scoped Manifold ContDiff RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** The radial covector obeys the Cauchy bound for the actual cap
metric, including the tip. No Euclidean lower bound on the metric is assumed. -/
theorem RoundCapProfile.globalMetric_radial_cauchy (P : RoundCapProfile)
    (x v : E3) :
    (inner ℝ x v) ^ 2 ≤ ‖x‖ ^ 2 * P.globalMetric.metricInner x v v := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hcs : (inner ℝ x v) ^ 2 ≤ ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
      simpa only [← sq, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le x v
    have halg : ‖x‖ ^ 2 * P.globalMetric.metricInner x v v - (inner ℝ x v)^2 =
        (P.w ‖x‖ / ‖x‖)^2 * (‖x‖^2 * ‖v‖^2 - (inner ℝ x v)^2) := by
      rw [P.globalMetric_formula x hx v v, real_inner_self_eq_norm_sq]
      field_simp
      <;> ring
    have hpos := mul_nonneg (sq_nonneg (P.w ‖x‖ / ‖x‖)) (sub_nonneg.mpr hcs)
    linarith

/-- **Math.** Smooth regularization of the radius has radial differential
bounded by the actual cap speed, uniformly in the positive regularizer. -/
theorem RoundCapProfile.globalMetric_regularized_radial_bound
    (P : RoundCapProfile) (e : ℝ) (he : 0 < e) (x v : E3) :
    |inner ℝ x v / Real.sqrt (‖x‖^2 + e^2)| ≤
      Real.sqrt (P.globalMetric.metricInner x v v) := by
  have hq := P.globalMetric.metricInner_self_nonneg x v
  have hd : 0 < ‖x‖^2 + e^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos he)
  have hden : 0 < Real.sqrt (‖x‖^2 + e^2) := Real.sqrt_pos.mpr hd
  have hcs : (inner ℝ x v)^2 ≤
      (‖x‖^2 + e^2) * P.globalMetric.metricInner x v v := by
    have hr := P.globalMetric_radial_cauchy x v
    have ha := mul_nonneg (sq_nonneg e) hq
    nlinarith
  have hs := Real.sqrt_le_sqrt hcs
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul hd.le] at hs
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  simpa only [mul_comm] using hs

end MorganTianLib.SurgeryCap
