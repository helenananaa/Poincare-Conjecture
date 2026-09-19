import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Nonnegativity of every vector in a real quadratic plane controls its determinant. -/
theorem quadratic_nonneg_det (a b c : ℝ)
    (h : ∀ s t : ℝ, 0 ≤ a*s^2 + 2*b*s*t + c*t^2) :
    0 ≤ a ∧ 0 ≤ c ∧ b^2 ≤ a*c :=
/- SWARM_PROOF_BEGIN -/
by
  -- Nonnegativity on the coordinate axes: (s,t)=(1,0) and (0,1).
  have ha : 0 ≤ a := by
    simpa using h 1 0
  have hc : 0 ≤ c := by
    simpa using h 0 1
  refine ⟨ha, hc, ?_⟩
  rcases lt_or_eq_of_le ha with hapos | rfl
  · -- a > 0: evaluate at s = -b, t = a and cancel a.
    have hval := h (-b) a
    have hrw :
        a * (-b) ^ 2 + 2 * b * (-b) * a + c * a ^ 2 = a * (a * c - b ^ 2) := by
      ring
    rw [hrw] at hval
    have hdisc : 0 ≤ a * c - b ^ 2 :=
      nonneg_of_mul_nonneg_right hval hapos
    exact sub_nonneg.mp hdisc
  · -- a = 0: force b = 0 by choosing s of the sign opposite to b.
    rcases lt_trichotomy b 0 with hb | rfl | hb
    · -- b < 0: take the positive value s = (-c - 1) / (2 * b).
      have hbne : b ≠ 0 := hb.ne
      have h2b : (2 : ℝ) * b ≠ 0 := mul_ne_zero two_ne_zero hbne
      have hval := h ((-c - 1) / (2 * b)) 1
      have hlin :
          (2 : ℝ) * b * ((-c - 1) / (2 * b)) + c = -1 := by
        field_simp [h2b]
        ring
      have hneg : (0 : ℝ) ≤ -1 := by
        simpa [hlin] using hval
      exact (not_le_of_gt (by norm_num : (-1 : ℝ) < 0) hneg).elim
    · simp
    · -- b > 0: take the negative value s = (-c - 1) / (2 * b).
      have hbne : b ≠ 0 := hb.ne'
      have h2b : (2 : ℝ) * b ≠ 0 := mul_ne_zero two_ne_zero hbne
      have hval := h ((-c - 1) / (2 * b)) 1
      have hlin :
          (2 : ℝ) * b * ((-c - 1) / (2 * b)) + c = -1 := by
        field_simp [h2b]
        ring
      have hneg : (0 : ℝ) ≤ -1 := by
        simpa [hlin] using hval
      exact (not_le_of_gt (by norm_num : (-1 : ℝ) < 0) hneg).elim
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
