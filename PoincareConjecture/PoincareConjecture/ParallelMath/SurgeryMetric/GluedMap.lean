import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- Compatible maps on a covering family define a map with the exact given restrictions. -/
theorem exists_map_of_compatible_cover {ι X Y : Type*}
    (S : ι → Set X) (hcover : ∀ x : X, ∃ i, x ∈ S i)
    (f : ι → X → Y)
    (hcompat : ∀ i j x, x ∈ S i → x ∈ S j → f i x = f j x) :
    ∃ F : X → Y, ∀ i x, x ∈ S i → F x = f i x :=
/- SWARM_PROOF_BEGIN -/
by
  choose i hi using hcover
  refine ⟨fun x => f (i x) x, ?_⟩
  intro j x hx
  exact hcompat (i x) j x (hi x) hx
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
