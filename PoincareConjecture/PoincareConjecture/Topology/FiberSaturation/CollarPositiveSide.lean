import PoincareConjecture.Topology.FiberSaturation.OneSidedCollar
import Mathlib.Tactic

set_option autoImplicit false
namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- Once a central point contacts a complementary frontier, the positive
half of its genuine collar is exactly that complementary component locally. -/
theorem oneSidedCollar_mem_component_iff_pos
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PreconnectedSpace X]
    {C : Set Y} {f : X × NeckParameter → Y} (hf : Topology.IsOpenEmbedding f)
    (hside : ∀ z, f z ∈ C ↔ (z.2 : ℝ) ≤ 0) {p : Y} {x : X}
    (hx : f (x, neckCenter) ∈ frontier (connectedComponentIn Cᶜ p))
    (z : X × NeckParameter) :
    f z ∈ connectedComponentIn Cᶜ p ↔ 0 < (z.2 : ℝ) :=
/- SWARM_PROOF_BEGIN -/
by
  let S := f '' positiveCollar X
  have hS : IsPreconnected S :=
    isPreconnected_positiveCollar.image f hf.continuous.continuousOn
  have hSC : S ⊆ Cᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hC
    exact (not_le.mpr hz.2.1) ((hside z).mp hC)
  have hVS : range f ∩ Cᶜ ⊆ S := by
    rintro _ ⟨⟨z, rfl⟩, hz⟩
    refine ⟨z, ⟨mem_univ _, ?_, z.2.property.2⟩, rfl⟩
    exact lt_of_not_ge (fun ht => hz ((hside z).mpr ht))
  have hSD : S ⊆ connectedComponentIn Cᶜ p :=
    exterior_piece_subset_component hS hSC hf.isOpen_range
      (mem_range_self (x, neckCenter)) (frontier_subset_closure hx) hVS
  constructor
  · intro hz
    have hzC := connectedComponentIn_subset Cᶜ p hz
    exact lt_of_not_ge (fun ht => hzC ((hside z).mpr ht))
  · intro hz
    exact hSD ⟨z, ⟨mem_univ _, hz, z.2.property.2⟩, rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation
