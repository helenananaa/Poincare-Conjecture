import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function
open scoped Topology RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Operator-norm perturbations preserve half the original positive lower bound. -/
theorem coercivity_survives_operator_perturbation (A B : E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0<c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hAB : ‖B-A‖ ≤ c/2) :
    ∀ v : E3, (c/2)*‖v‖^2 ≤ inner ℝ (B v) v :=
/- SWARM_PROOF_BEGIN -/
by
  intro v
  have hdiff : ‖(B - A) v‖ ≤ ‖B - A‖ * ‖v‖ := (B - A).le_opNorm v
  have hquad : |inner ℝ ((B - A) v) v| ≤ ‖B - A‖ * ‖v‖ ^ 2 := by
    calc
      |inner ℝ ((B - A) v) v| ≤ ‖(B - A) v‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (‖B - A‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
      _ = ‖B - A‖ * ‖v‖ ^ 2 := by ring
  have hquad_lower : -(c / 2) * ‖v‖ ^ 2 ≤ inner ℝ ((B - A) v) v := by
    calc
      -(c / 2) * ‖v‖ ^ 2 = -(c / 2 * ‖v‖ ^ 2) := by ring
      _ ≤ -(‖B - A‖ * ‖v‖ ^ 2) := by
        exact neg_le_neg (mul_le_mul_of_nonneg_right hAB (sq_nonneg ‖v‖))
      _ ≤ -|inner ℝ ((B - A) v) v| := neg_le_neg hquad
      _ ≤ inner ℝ ((B - A) v) v := neg_abs_le _
  calc
    (c / 2) * ‖v‖ ^ 2 ≤ c * ‖v‖ ^ 2 + (-(c / 2) * ‖v‖ ^ 2) := by
      ring_nf
      exact le_rfl
    _ ≤ inner ℝ (A v) v + inner ℝ ((B - A) v) v :=
      add_le_add (hA v) hquad_lower
    _ = inner ℝ (A v + (B - A) v) v := by rw [inner_add_left]
    _ = inner ℝ (B v) v := by congr 1 <;> simp [sub_eq_add_neg]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
