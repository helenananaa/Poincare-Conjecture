import PoincareConjecture.ParallelImplementation.BoundedSubmoduleRestriction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.RestrictedRightInverse
/-- Assemble the restricted right inverse using ambient equalities. -/
theorem exists_restricted_right_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (X : Submodule ℝ F) (Y : Submodule ℝ E)
    (D : X →L[ℝ] Y) (hmap : ∀ y : E, y ∈ Y → A y ∈ X)
    (hAD : ∀ x : X, A (D x : E) = (x : F)) :
    ∃ L : Y →L[ℝ] X, ‖L‖ ≤ ‖A‖ ∧
      L.comp D = ContinuousLinearMap.id ℝ X ∧
      ∀ y : Y, (L y : F) = A (y : E) := by
  obtain ⟨L, hLnorm, hLapply⟩ :=
    PoincareConjecture.ParallelImplementation.BoundedSubmoduleRestriction.exists_bounded_submodule_restriction A Y X hmap
  refine ⟨L, hLnorm, ?_, hLapply⟩
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change (L (D x) : F) = (x : F)
  rw [hLapply]
  exact hAD x
end PoincareConjecture.ParallelImplementation.RestrictedRightInverse
