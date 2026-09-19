import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Uniform parameterwise bounds pass to a bounded sweepout supremum. -/
theorem peakCost_transport {B C : Type*} [Nonempty B] [Nonempty C]
    (f : B → ℝ) (g : C → ℝ) (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (T : B → C) (hsurj : Surjective T) (L δ : ℝ) (hL : 0 ≤ L)
    (hcost : ∀ b, g (T b) ≤ L * f b + δ) :
    peakCost g ≤ L * peakCost f + δ :=
/- SWARM_PROOF_BEGIN -/
by
  refine (csSup_le_iff hg (range_nonempty g)).mpr ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨b, rfl⟩ := hsurj c
  calc
    g (T b) ≤ L * f b + δ := hcost b
    _ ≤ L * peakCost f + δ :=
      add_le_add_left (mul_le_mul_of_nonneg_left (le_csSup hf (mem_range_self b)) hL) δ
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
