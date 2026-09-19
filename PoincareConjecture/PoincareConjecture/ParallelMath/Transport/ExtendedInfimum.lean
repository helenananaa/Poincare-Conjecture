import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Positive finite constants commute with infima, including an empty admissible family. -/
theorem ennreal_infimum_twoSided {A : Type*} (f g : A → ℝ≥0∞)
    (l u : ℝ≥0∞) (hl0 : l ≠ 0) (hlt : l ≠ ⊤) (hu0 : u ≠ 0) (hut : u ≠ ⊤)
    (h : ∀ a, l * f a ≤ g a ∧ g a ≤ u * f a) :
    l * (⨅ a, f a) ≤ (⨅ a, g a) ∧ (⨅ a, g a) ≤ u * (⨅ a, f a) :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · rw [ENNReal.mul_iInf_of_ne hl0 hlt]
    exact iInf_mono fun a => (h a).1
  · rw [ENNReal.mul_iInf_of_ne hu0 hut]
    exact iInf_mono fun a => (h a).2
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
