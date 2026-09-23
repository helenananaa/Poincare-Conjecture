import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** gaussian shift polynomial. -/
theorem gaussian_shift_polynomial 
    (a t alpha : ℝ) (ha : 0 ≤ a) (ht : 0 < t) (halpha : 0 < alpha) :
    ((a+Real.sqrt t)/t^2+(a+Real.sqrt t)^3/t^3)*a^alpha =
      2*a^alpha/t^((3:ℝ)/2) + 4*a^(alpha+1)/t^2 +
      3*a^(alpha+2)/t^((5:ℝ)/2) + a^(alpha+3)/t^3 :=
/- SWARM_PROOF_BEGIN -/
by
  by_cases ha0 : a = 0
  · subst a
    have hα0 : alpha ≠ 0 := ne_of_gt halpha
    have hα1 : alpha + 1 ≠ 0 := by linarith
    have hα2 : alpha + 2 ≠ 0 := by linarith
    have hα3 : alpha + 3 ≠ 0 := by linarith
    simp [Real.zero_rpow, hα0, hα1, hα2, hα3]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have ha1 : a ^ (alpha + 1) = a ^ alpha * a := by
      rw [Real.rpow_add ha_pos alpha 1, Real.rpow_one]
    have ha2 : a ^ (alpha + 2) = a ^ alpha * a ^ 2 := by
      rw [Real.rpow_add ha_pos alpha 2]
      exact congrArg (a ^ alpha * ·) (by simpa using Real.rpow_natCast a 2)
    have ha3 : a ^ (alpha + 3) = a ^ alpha * a ^ 3 := by
      rw [Real.rpow_add ha_pos alpha 3]
      exact congrArg (a ^ alpha * ·) (by simpa using Real.rpow_natCast a 3)
    have ht3 : t ^ ((3 : ℝ) / 2) = t * Real.sqrt t := by
      rw [show (3 : ℝ) / 2 = (1 : ℝ) + (1 : ℝ) / 2 by ring,
        Real.rpow_add ht, Real.rpow_one, ← Real.sqrt_eq_rpow t]
    have ht5 : t ^ ((5 : ℝ) / 2) = t ^ 2 * Real.sqrt t := by
      rw [show (5 : ℝ) / 2 = (2 : ℝ) + (1 : ℝ) / 2 by ring,
        Real.rpow_add ht, ← Real.sqrt_eq_rpow t]
      exact congrArg (· * Real.sqrt t) (by simpa using Real.rpow_natCast t 2)
    rw [ha1, ha2, ha3, ht3, ht5]
    field_simp [ne_of_gt ht, ne_of_gt (Real.sqrt_pos.2 ht)]
    nlinarith [Real.sq_sqrt (le_of_lt ht)]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
