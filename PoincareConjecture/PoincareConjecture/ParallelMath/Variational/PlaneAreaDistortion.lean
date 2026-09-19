import PoincareConjecture.ParallelMath.Variational.QuadraticDiscriminant
import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- A genuine quadratic-form distortion on an orthonormal two-plane bounds its area Jacobian. -/
theorem plane_area_distortion (a b c ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (h : ∀ s t : ℝ, (1-ε)*(s^2+t^2) ≤ a*s^2 + 2*b*s*t + c*t^2 ∧
      a*s^2 + 2*b*s*t + c*t^2 ≤ (1+ε)*(s^2+t^2)) :
    1-ε ≤ Real.sqrt (a*c-b^2) ∧ Real.sqrt (a*c-b^2) ≤ 1+ε :=
/- SWARM_PROOF_BEGIN -/
by
  -- Lower-shifted quadratic form is nonnegative.
  have hshift : ∀ s t : ℝ,
      0 ≤ (a - (1 - ε)) * s ^ 2 + 2 * b * s * t + (c - (1 - ε)) * t ^ 2 := by
    intro s t
    have hlo := (h s t).1
    have heq :
        (a - (1 - ε)) * s ^ 2 + 2 * b * s * t + (c - (1 - ε)) * t ^ 2
          = a * s ^ 2 + 2 * b * s * t + c * t ^ 2 - (1 - ε) * (s ^ 2 + t ^ 2) := by
      ring
    rw [heq]
    exact sub_nonneg.mpr hlo
  have hnn := quadratic_nonneg_det (a - (1 - ε)) b (c - (1 - ε)) hshift
  have ha_lo : 1 - ε ≤ a := sub_nonneg.mp hnn.1
  have hc_lo : 1 - ε ≤ c := sub_nonneg.mp hnn.2.1
  have h1me : 0 ≤ 1 - ε := sub_nonneg.mpr hε1.le
  have h1pe : 0 ≤ 1 + ε := add_nonneg zero_le_one hε0
  -- Diagonal upper bounds from the axes (s,t)=(1,0) and (0,1).
  have ha_hi : a ≤ 1 + ε := by
    simpa using (h 1 0).2
  have hc_hi : c ≤ 1 + ε := by
    simpa using (h 0 1).2
  have hc0 : 0 ≤ c := h1me.trans hc_lo
  have hac_hi : a * c ≤ (1 + ε) * (1 + ε) :=
    mul_le_mul ha_hi hc_hi hc0 h1pe
  have hdet_hi : a * c - b ^ 2 ≤ (1 + ε) ^ 2 := by
    calc
      a * c - b ^ 2 ≤ a * c := sub_le_self _ (sq_nonneg b)
      _ ≤ (1 + ε) * (1 + ε) := hac_hi
      _ = (1 + ε) ^ 2 := (pow_two (1 + ε)).symm
  -- Shifted determinant identity plus the trace lower bound a+c ≥ 2(1-ε).
  have hprod :
      (a - (1 - ε)) * (c - (1 - ε))
        = a * c - (1 - ε) * (a + c) + (1 - ε) ^ 2 := by
    ring
  have hdisc : b ^ 2 ≤ a * c - (1 - ε) * (a + c) + (1 - ε) ^ 2 := by
    rw [← hprod]
    exact hnn.2.2
  have htrace : 2 * (1 - ε) ≤ a + c := by
    linarith [ha_lo, hc_lo]
  have hdet_lo : (1 - ε) ^ 2 ≤ a * c - b ^ 2 := by
    calc
      (1 - ε) ^ 2
          = (1 - ε) * (2 * (1 - ε)) - (1 - ε) ^ 2 := by
            ring
      _ ≤ (1 - ε) * (a + c) - (1 - ε) ^ 2 :=
          sub_le_sub_right (mul_le_mul_of_nonneg_left htrace h1me) _
      _ ≤ a * c - b ^ 2 := by
          linarith [hdisc]
  constructor
  · have hsqrt := Real.sqrt_le_sqrt hdet_lo
    rwa [Real.sqrt_sq h1me] at hsqrt
  · have hsqrt := Real.sqrt_le_sqrt hdet_hi
    rwa [Real.sqrt_sq h1pe] at hsqrt
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
