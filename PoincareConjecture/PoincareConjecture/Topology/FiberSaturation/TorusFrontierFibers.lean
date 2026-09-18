import PoincareConjecture.Topology.FiberSaturation.AbstractBundleRegion

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set

/-- The actual frontier in the orbit quotient is exactly two distinct fibers
of its circle projection, not merely an abstract pair of sphere-like sets. -/
theorem region_frontier_circle_pair {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (φ : X ≃ₜ X) {L : ℝ} (hL : 0 < L)
    {D : Set (Space φ L)} (ho : IsOpen D) (hc : IsConnected D)
    (hs : FiberSaturated (proj φ L ⁻¹' frontier D))
    (hn : (frontier (closure D)).Nonempty) :
    ∃ u v : AddCircle L, u ≠ v ∧
      frontier D = circleProjection φ L ⁻¹' ({u,v} : Set (AddCircle L)) := by
  obtain ⟨a,b,hab,hw,hD,hcl⟩ := region_short_strip φ hL ho hc hs hn
  have hsub : ((univ : Set X) ×ˢ Ioo a b) ⊆ univ ×ˢ Icc a b :=
    prod_mono (Subset.refl _) Ioo_subset_Icc_self
  have hfront : frontier D = proj φ L '' ((univ : Set X) ×ˢ ({a,b} : Set ℝ)) := by
    rw [ho.frontier_eq, hcl, hD,
      ← (proj_injOn_closedStrip φ hL hw).image_sdiff_subset hsub]
    simp [prod_sdiff_prod, Icc_sdiff_Ioo_same hab.le]
  refine ⟨(a : AddCircle L), (b : AddCircle L), ?_, ?_⟩
  · intro he
    obtain ⟨n,hn⟩ := circle_eq_iff_integer_shift.mp he
    have hn0 := integer_shift_zero hL hw ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ hn
    have he' : a = b := by simpa [hn0] using hn
    exact hab.ne he'
  · have hpair : ((univ : Set X) ×ˢ ({a,b} : Set ℝ)) =
        (univ ×ˢ ({a} : Set ℝ)) ∪ (univ ×ˢ ({b} : Set ℝ)) := by
      ext p
      simp
    rw [hfront, hpair, image_union, image_height_fiber, image_height_fiber]
    ext z
    simp

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
