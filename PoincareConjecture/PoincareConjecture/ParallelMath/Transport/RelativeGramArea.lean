import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.ParallelMath.Transport.PSDDetMonotone

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Quadratic-form distortion gives relative Gram area distortion without any reference orthonormality. -/
theorem relative_gram_area_distortion (a0 b0 c0 a b c epsilon : ℝ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    (h0 : ∀ s t : ℝ, 0 ≤ a0*s^2 + 2*b0*s*t + c0*t^2)
    (h : ∀ s t : ℝ,
      (1-epsilon)*(a0*s^2+2*b0*s*t+c0*t^2) ≤ a*s^2+2*b*s*t+c*t^2 ∧
      a*s^2+2*b*s*t+c*t^2 ≤ (1+epsilon)*(a0*s^2+2*b0*s*t+c0*t^2)) :
    (1-epsilon)*Real.sqrt (a0*c0-b0^2) ≤ Real.sqrt (a*c-b^2) ∧
      Real.sqrt (a*c-b^2) ≤ (1+epsilon)*Real.sqrt (a0*c0-b0^2) :=
/- SWARM_PROOF_BEGIN -/
by
  have h1me : 0 ≤ 1 - epsilon := sub_nonneg.mpr he1.le
  have h1pe : 0 ≤ 1 + epsilon := add_nonneg zero_le_one he0
  -- Nonnegativity of A0 controls its determinant (including the degenerate case).
  have h0det :=
    PoincareConjecture.ParallelMath.Variational.quadratic_nonneg_det a0 b0 c0 h0
  have hdet0 : 0 ≤ a0 * c0 - b0 ^ 2 := sub_nonneg.mpr h0det.2.2
  -- Scaling identities for the quadratic form and its determinant.
  have hform (mu s t : ℝ) :
      (mu * a0) * s ^ 2 + 2 * (mu * b0) * s * t + (mu * c0) * t ^ 2
        = mu * (a0 * s ^ 2 + 2 * b0 * s * t + c0 * t ^ 2) := by
    ring
  have hdet_scale (mu : ℝ) :
      (mu * a0) * (mu * c0) - (mu * b0) ^ 2
        = mu ^ 2 * (a0 * c0 - b0 ^ 2) := by
    ring
  -- (1-ε)A0 is PSD, and (1-ε)A0 ≤ A ≤ (1+ε)A0.
  have hlo_psd : ∀ s t : ℝ,
      0 ≤ ((1 - epsilon) * a0) * s ^ 2 + 2 * ((1 - epsilon) * b0) * s * t
        + ((1 - epsilon) * c0) * t ^ 2 := by
    intro s t
    rw [hform]
    exact mul_nonneg h1me (h0 s t)
  have hlo : ∀ s t : ℝ,
      ((1 - epsilon) * a0) * s ^ 2 + 2 * ((1 - epsilon) * b0) * s * t
        + ((1 - epsilon) * c0) * t ^ 2
        ≤ a * s ^ 2 + 2 * b * s * t + c * t ^ 2 := by
    intro s t
    rw [hform]
    exact (h s t).1
  have hA : ∀ s t : ℝ, 0 ≤ a * s ^ 2 + 2 * b * s * t + c * t ^ 2 := by
    intro s t
    exact (hlo_psd s t).trans (hlo s t)
  have hhi : ∀ s t : ℝ,
      a * s ^ 2 + 2 * b * s * t + c * t ^ 2
        ≤ ((1 + epsilon) * a0) * s ^ 2 + 2 * ((1 + epsilon) * b0) * s * t
          + ((1 + epsilon) * c0) * t ^ 2 := by
    intro s t
    rw [hform]
    exact (h s t).2
  -- Determinant monotonicity, even if A0 is singular.
  have hdet_lo :=
    psd2_determinant_monotone ((1 - epsilon) * a0) ((1 - epsilon) * b0)
      ((1 - epsilon) * c0) a b c hlo_psd hlo
  have hdet_hi :=
    psd2_determinant_monotone a b c ((1 + epsilon) * a0) ((1 + epsilon) * b0)
      ((1 + epsilon) * c0) hA hhi
  rw [hdet_scale (1 - epsilon)] at hdet_lo
  rw [hdet_scale (1 + epsilon)] at hdet_hi
  constructor
  · have hsqrt := Real.sqrt_le_sqrt hdet_lo
    rwa [Real.sqrt_mul' _ hdet0, Real.sqrt_sq h1me] at hsqrt
  · have hsqrt := Real.sqrt_le_sqrt hdet_hi
    rwa [Real.sqrt_mul' _ hdet0, Real.sqrt_sq h1pe] at hsqrt
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
