import PoincareConjecture.Topology.FiberSaturation.TorusLiftedRegion

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set
variable {X : Type*} [TopologicalSpace X]

/-- Projection forgets every integer deck translate of a set. -/
theorem proj_image_deck (φ : X ≃ₜ X) (L : ℝ) (n : ℤ) (S : Set (X × ℝ)) :
    proj φ L '' ((deck φ L n) '' S) = proj φ L '' S := by
  rw [image_image]
  simp only [proj_deck]

/-- Projected components either coincide or are disjoint. An intersection
is converted to a genuine integer deck identification of representatives. -/
theorem component_images_eq_of_inter (φ : X ≃ₜ X) (L : ℝ)
    (D : Set (Space φ L)) {p r : X × ℝ}
    (hp : p ∈ proj φ L ⁻¹' D)
    (hmeet : ((proj φ L '' connectedComponentIn (proj φ L ⁻¹' D) p) ∩
      (proj φ L '' connectedComponentIn (proj φ L ⁻¹' D) r)).Nonempty) :
    proj φ L '' connectedComponentIn (proj φ L ⁻¹' D) p =
      proj φ L '' connectedComponentIn (proj φ L ⁻¹' D) r := by
  obtain ⟨z, ⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩ := hmeet
  obtain ⟨n, hn⟩ := (proj_eq_iff φ L x y).mp (hxz.trans hyz.symm)
  have htransport := (deck φ L n).image_connectedComponentIn hp
  rw [deck_image_preimage] at htransport
  have hy' : y ∈ connectedComponentIn (proj φ L ⁻¹' D) (deck φ L n p) := by
    rw [← htransport]
    exact ⟨x, hx, hn⟩
  have heq := (connectedComponentIn_eq hy').trans (connectedComponentIn_eq hy).symm
  calc
    proj φ L '' connectedComponentIn (proj φ L ⁻¹' D) p =
        proj φ L '' ((deck φ L n) '' connectedComponentIn (proj φ L ⁻¹' D) p) :=
      (proj_image_deck φ L n _).symm
    _ = proj φ L '' connectedComponentIn (proj φ L ⁻¹' D) r := by
      rw [htransport, heq]

/-- A selected lifted component covers the entire connected quotient region.
This does not assume path lifting or surjectivity of that component. -/
theorem image_lifted_component_eq [PreconnectedSpace X] (φ : X ≃ₜ X)
    (L : ℝ) {D : Set (Space φ L)} (hD : IsOpen D) (hc : IsPreconnected D)
    (hs : FiberSaturated (proj φ L ⁻¹' D)) {p : X × ℝ}
    (hp : p ∈ proj φ L ⁻¹' D) :
    proj φ L '' connectedComponentIn (proj φ L ⁻¹' D) p = D := by
  let V : Set (Space φ L) := proj φ L '' connectedComponentIn (proj φ L ⁻¹' D) p
  have hopen : IsOpen V := isOpenMap_proj φ L _ (lifted_component_isOpen φ L hD hs hp)
  have hsub : V ⊆ D := by
    rintro z ⟨q, hq, rfl⟩
    exact connectedComponentIn_subset (proj φ L ⁻¹' D) p hq
  apply Subset.antisymm hsub
  apply hc.subset_of_closure_inter_subset hopen
    ⟨proj φ L p, hp, ⟨p, mem_connectedComponentIn hp, rfl⟩⟩
  rintro z ⟨hzcl, hzD⟩
  obtain ⟨r, rfl⟩ := proj_surjective φ L z
  have hr : r ∈ proj φ L ⁻¹' D := hzD
  let Vr : Set (Space φ L) := proj φ L '' connectedComponentIn (proj φ L ⁻¹' D) r
  have hro : IsOpen Vr := isOpenMap_proj φ L _ (lifted_component_isOpen φ L hD hs hr)
  have hrmem : proj φ L r ∈ Vr := ⟨r, mem_connectedComponentIn hr, rfl⟩
  have hmeet : (Vr ∩ V).Nonempty := mem_closure_iff.mp hzcl Vr hro hrmem
  have heq : Vr = V := component_images_eq_of_inter φ L D hr hmeet
  rw [← heq]
  exact hrmem

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
