import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- A uniform additive cost perturbation controls infima even without minimizers. -/
theorem leastCost_uniform_perturbation {A : Type*} [Nonempty A]
    (f g : A → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a)
    (δ : ℝ) (hδ : 0 ≤ δ) (hclose : ∀ a, |f a - g a| ≤ δ) :
    |leastCost f - leastCost g| ≤ δ :=
/- SWARM_PROOF_BEGIN -/
by
  have _ := hδ
  have hfB : BddBelow (range f) := ⟨0, by rintro _ ⟨a, rfl⟩; exact hf a⟩
  have hgB : BddBelow (range g) := ⟨0, by rintro _ ⟨a, rfl⟩; exact hg a⟩
  have hinf_le {u v : A → ℝ} (huB : BddBelow (range u))
      (huv : ∀ a, u a ≤ v a + δ) : leastCost u ≤ leastCost v + δ := by
    unfold leastCost
    have : sInf (range u) - δ ≤ sInf (range v) := by
      refine le_csInf (range_nonempty _) ?_
      rintro _ ⟨a, rfl⟩
      have : sInf (range u) ≤ u a := csInf_le huB (mem_range_self a)
      linarith [huv a]
    linarith
  have hfδ : ∀ a, f a ≤ g a + δ := fun a => by
    have := (abs_le.mp (hclose a)).2
    linarith
  have hgδ : ∀ a, g a ≤ f a + δ := fun a => by
    have := (abs_le.mp (hclose a)).1
    linarith
  have hfg := hinf_le hfB hfδ
  have hgf := hinf_le hgB hgδ
  rw [abs_le]
  constructor <;> linarith
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
