import Mathlib.GroupTheory.CoprodI

set_option autoImplicit false

namespace PoincareConjecture.ParallelMath
open Monoid

/-- If an indexed free product is the trivial group, every factor is trivial.

Blueprint: `lem:trivial-free-product-factors`. Pure group theory: no manifold,
van Kampen, or connected-sum content. -/
theorem coprodI_trivial_implies_factor_trivial
    {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    (h : ∀ x : CoprodI G, x = 1) (i : ι) (g : G i) : g = 1 := by
  have h1 : (CoprodI.of : G i →* CoprodI G) g = 1 := h _
  rw [← map_one (CoprodI.of : G i →* CoprodI G)] at h1
  exact CoprodI.of_injective i h1

end PoincareConjecture.ParallelMath
