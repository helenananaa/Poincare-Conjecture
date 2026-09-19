import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.ParallelMath.Transport.PSDMixed
import PoincareConjecture.ParallelMath.Variational.QuadraticDiscriminant

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Loewner order on positive-semidefinite 2 by 2 forms implies determinant order, even if singular. -/
theorem psd2_determinant_monotone (a b c d e f : ℝ)
    (hA : ∀ s t : ℝ, 0 ≤ a*s^2 + 2*b*s*t + c*t^2)
    (hAB : ∀ s t : ℝ, a*s^2 + 2*b*s*t + c*t^2 ≤ d*s^2 + 2*e*s*t + f*t^2) :
    a*c-b^2 ≤ d*f-e^2 :=
/- SWARM_PROOF_BEGIN -/
by
  -- Nonnegativity of A controls its diagonal entries and determinant.
  have hAdet :=
    PoincareConjecture.ParallelMath.Variational.quadratic_nonneg_det a b c hA
  -- The Loewner gap B-A is itself a nonnegative quadratic form.
  have hBAform : ∀ s t : ℝ,
      0 ≤ (d - a) * s ^ 2 + 2 * (e - b) * s * t + (f - c) * t ^ 2 := by
    intro s t
    have h := hAB s t
    have heq :
        (d - a) * s ^ 2 + 2 * (e - b) * s * t + (f - c) * t ^ 2
          = (d * s ^ 2 + 2 * e * s * t + f * t ^ 2)
            - (a * s ^ 2 + 2 * b * s * t + c * t ^ 2) := by
      ring
    rw [heq]
    exact sub_nonneg.mpr h
  have hBAdet :=
    PoincareConjecture.ParallelMath.Variational.quadratic_nonneg_det
      (d - a) (e - b) (f - c) hBAform
  -- Mixed determinant of the pair (A, B-A) is nonnegative.
  have hmixed :=
    psd2_mixed_determinant_nonneg a b c (d - a) (e - b) (f - c)
      hAdet.1 hAdet.2.1 hBAdet.1 hBAdet.2.1 hAdet.2.2 hBAdet.2.2
  have hBAnn : 0 ≤ (d - a) * (f - c) - (e - b) ^ 2 :=
    sub_nonneg.mpr hBAdet.2.2
  -- det(B) expands as det(A) + det(B-A) + mixed.
  have hident :
      d * f - e ^ 2
        = (a * c - b ^ 2)
          + ((d - a) * (f - c) - (e - b) ^ 2)
          + (a * (f - c) + c * (d - a) - 2 * b * (e - b)) := by
    ring
  linarith
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
