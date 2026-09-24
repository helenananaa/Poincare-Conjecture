import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BoundedSubmoduleRestriction
/-- Restrict a bounded operator to invariant source and target submodules. -/
theorem exists_bounded_submodule_restriction
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (S : Submodule ℝ E) (T : Submodule ℝ F)
    (hmap : ∀ x : E, x ∈ S → A x ∈ T) :
    ∃ L : S →L[ℝ] T, ‖L‖ ≤ ‖A‖ ∧ ∀ s : S, (L s : F) = A (s : E) := by
  let L : S →L[ℝ] T :=
    (A.comp S.subtypeL).codRestrict T (fun s => hmap s.1 s.2)
  refine ⟨L, ?_, ?_⟩
  · apply L.opNorm_le_bound (norm_nonneg A)
    intro s
    change ‖A s.1‖ ≤ ‖A‖ * ‖s.1‖
    exact A.le_opNorm s.1
  · intro s
    rfl
end PoincareConjecture.ParallelImplementation.BoundedSubmoduleRestriction
