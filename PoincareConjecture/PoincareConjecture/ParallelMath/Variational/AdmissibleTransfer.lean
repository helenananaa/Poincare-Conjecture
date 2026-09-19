import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- A map of admissible families with controlled costs transports their infima.
The family map need not be injective, surjective, or attain either infimum. -/
theorem leastCost_transfer {A B : Type*} [Nonempty A] [Nonempty B]
    (f : A → ℝ) (g : B → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ b, 0 ≤ g b)
    (T : A → B) (L δ : ℝ) (hL : 0 ≤ L)
    (hcost : ∀ a, g (T a) ≤ L * f a + δ) :
    leastCost g ≤ L * leastCost f + δ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  by_cases hbad : ∃ a, f a < 0
  · obtain ⟨a, ha⟩ := hbad
    exact ((not_lt_of_ge (hf a)) ha).elim
  ·
    have hg_bdd : BddBelow (range g) := ⟨0, by rintro _ ⟨b, rfl⟩; exact hg b⟩
    have hbound : ∀ a, leastCost g ≤ L * f a + δ := fun a =>
      (ciInf_le hg_bdd (T a)).trans (hcost a)
    rcases eq_or_lt_of_le hL with hL0 | hLpos
    · subst hL0
      obtain ⟨a⟩ := ‹Nonempty A›
      simpa using hbound a
    · have hdiv : ∀ a, (leastCost g - δ) / L ≤ f a := fun a =>
        (div_le_iff₀ hLpos).mpr <| by
          rw [mul_comm]
          exact sub_le_iff_le_add.mpr (hbound a)
      have hinf : (leastCost g - δ) / L ≤ leastCost f := le_ciInf hdiv
      have : leastCost g - δ ≤ L * leastCost f := by
        rw [mul_comm]
        exact (div_le_iff₀ hLpos).mp hinf
      exact sub_le_iff_le_add.mp this
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
