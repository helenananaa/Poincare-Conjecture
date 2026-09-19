import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Nonnegative cost families have an infimum and epsilon minimizers, without attainment. -/
theorem leastCost_nonneg_and_approx {A : Type*} [Nonempty A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ leastCost f ∧ (∀ a, leastCost f ≤ f a) ∧
    ∀ ε : ℝ, 0 < ε → ∃ a, f a < leastCost f + ε :=
/- SWARM_PROOF_BEGIN -/
by
  have hne : (range f).Nonempty := range_nonempty f
  have hbdd : BddBelow (range f) := ⟨0, fun _ ⟨a, ha⟩ => ha ▸ hf a⟩
  refine ⟨?nonneg, ?lb, ?approx⟩
  · exact le_csInf hne fun _ ⟨a, ha⟩ => ha ▸ hf a
  · intro a
    exact csInf_le hbdd (mem_range_self a)
  · intro ε hε
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ :=
      (csInf_lt_iff hbdd hne).1 (lt_add_of_pos_right _ hε)
    exact ⟨a, ha⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
