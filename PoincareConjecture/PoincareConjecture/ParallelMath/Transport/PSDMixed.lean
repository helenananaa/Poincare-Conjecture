import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** The mixed determinant term of two positive-semidefinite 2 by 2 forms is nonnegative. -/
theorem psd2_mixed_determinant_nonneg (a b c d e f : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 ≤ f)
    (hb : b^2 ≤ a*c) (he : e^2 ≤ d*f) :
    0 ≤ a*f + c*d - 2*b*e :=
/- SWARM_PROOF_BEGIN -/
by
  set A := a * f
  set B := c * d
  have hA : 0 ≤ A := mul_nonneg ha hf
  have hB : 0 ≤ B := mul_nonneg hc hd
  have hbe2 : (b * e) ^ 2 ≤ A * B := by
    have hmul := mul_le_mul hb he (sq_nonneg e) (mul_nonneg ha hc)
    calc
      (b * e) ^ 2 = b ^ 2 * e ^ 2 := by ring
      _ ≤ (a * c) * (d * f) := hmul
      _ = A * B := by ring
  have h4AB : 4 * A * B ≤ (A + B) ^ 2 := four_mul_le_sq_add A B
  rcases le_or_gt (b * e) 0 with hle | hgt
  · -- If `b * e ≤ 0`, then `-2 * b * e ≥ 0`, so the mixed term is a sum of nonnegative quantities.
    nlinarith
  · -- Otherwise compare squares: `4 * (b * e) ^ 2 ≤ 4 * A * B ≤ (A + B) ^ 2`.
    have hsq : (2 * (b * e)) ^ 2 ≤ (A + B) ^ 2 := by
      calc
        (2 * (b * e)) ^ 2 = 4 * (b * e) ^ 2 := by ring
        _ ≤ 4 * (A * B) := mul_le_mul_of_nonneg_left hbe2 (by norm_num : (0 : ℝ) ≤ 4)
        _ = 4 * A * B := by ring
        _ ≤ (A + B) ^ 2 := h4AB
    have h2be : 2 * (b * e) ≤ A + B :=
      le_of_sq_le_sq hsq (add_nonneg hA hB)
    nlinarith
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
