import PoincareConjecture.Topology.FiberSaturation.CollarPositiveSide
import PoincareConjecture.Topology.FiberSaturation.CollarNegativeSide
import PoincareConjecture.Topology.FiberSaturation.OneSidedCollar
import Mathlib.Tactic

set_option autoImplicit false
namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- In a selected genuine collar, the complementary closure is exactly
the nonnegative half-space. This is local topology, not a global smooth atlas. -/
theorem oneSidedCollar_mem_closure_component_iff_nonneg
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PreconnectedSpace X]
    {C : Set Y} {f : X × NeckParameter → Y} (hf : Topology.IsOpenEmbedding f)
    (hside : ∀ z, f z ∈ C ↔ (z.2 : ℝ) ≤ 0) {p : Y} {x : X}
    (hx : f (x, neckCenter) ∈ frontier (connectedComponentIn Cᶜ p))
    (z : X × NeckParameter) :
    f z ∈ closure (connectedComponentIn Cᶜ p) ↔ 0 ≤ (z.2 : ℝ) :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · intro hz
    by_contra hnot
    have hneg : (z.2 : ℝ) < 0 := lt_of_not_ge hnot
    exact oneSidedCollar_negative_not_mem_closure hf hside z hneg hz
  · intro hz
    rcases hz.eq_or_lt with hzero | hz
    · have hzcenter : z.2 = neckCenter := by
        apply Subtype.ext
        exact hzero.symm
      have hzeq : z = (z.1, neckCenter) := by
        ext <;> simp [hzcenter]
      rw [hzeq]
      exact frontier_subset_closure (oneSidedCollar_frontier_saturated hf hside hx z.1)
    · exact subset_closure ((oneSidedCollar_mem_component_iff_pos hf hside hx z).mpr hz)
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation
