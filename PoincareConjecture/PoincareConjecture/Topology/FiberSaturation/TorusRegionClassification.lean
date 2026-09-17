import PoincareConjecture.Topology.FiberSaturation.TorusImageClosure

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set
variable {X : Type*} [TopologicalSpace X]

/-- Explicit unit-length normalization of an absolute closed cylinder. -/
def closedCylinderUnitHomeomorph {a b : ℝ} (hab : a < b) :
    ↥((univ : Set X) ×ˢ Icc a b) ≃ₜ (X × Icc (0 : ℝ) 1) :=
  (Homeomorph.Set.prod univ (Icc a b)).trans
    ((Homeomorph.Set.univ X).prodCongr (iccHomeoI a b hab))

/-- The three missing bridges are derived: finite lifted strip, coverage
of the whole region, and equality of the projected closure with its actual
closure. The nonempty frontier of closure is an explicit topological input. -/
theorem region_short_strip [PreconnectedSpace X] (φ : X ≃ₜ X)
    {L : ℝ} (hL : 0 < L) {D : Set (Space φ L)}
    (hD : IsOpen D) (hc : IsConnected D)
    (hfront : FiberSaturated (proj φ L ⁻¹' frontier D))
    (hf : (frontier (closure D)).Nonempty) :
    ∃ a b : ℝ, a < b ∧ b-a < L ∧
      D = proj φ L '' ((univ : Set X) ×ˢ Ioo a b) ∧
      closure D = proj φ L '' ((univ : Set X) ×ˢ Icc a b) := by
  have hs : FiberSaturated (proj φ L ⁻¹' D) := by
    apply fiberSaturated_of_frontier (hD.preimage (continuous_proj φ L))
    rwa [← (isOpenMap_proj φ L).preimage_frontier_eq_frontier_preimage
      (continuous_proj φ L)]
  have hproper : D ≠ univ := by
    intro h
    simp [h] at hf
  obtain ⟨z, hz⟩ := hc.nonempty
  obtain ⟨p, rfl⟩ := proj_surjective φ L z
  have hp : p ∈ proj φ L ⁻¹' D := hz
  letI : Nonempty X := ⟨p.1⟩
  obtain ⟨a, b, hab, hshape⟩ := lifted_component_finite_strip φ hL hD hproper hs hp
  have hu : proj φ L '' ((univ : Set X) ×ˢ Ioo a b) = D := by
    rw [← hshape]
    exact image_lifted_component_eq φ L hD hc.2 hs hp
  have hw : b-a < L := lifted_strip_component_width_lt φ hL D hp hshape (by rwa [hu])
  refine ⟨a, b, hab, hw, hu.symm, ?_⟩
  calc
    closure D = closure (proj φ L '' ((univ : Set X) ×ˢ Ioo a b)) := congrArg closure hu.symm
    _ = proj φ L '' ((univ : Set X) ×ˢ Icc a b) := closure_image_openStrip φ hL hab

/-- A genuine homeomorphism from the actual region closure, without assuming
a strip decomposition or surjectivity of a chosen lifted component. -/
theorem region_closure_homeomorph [PreconnectedSpace X] (φ : X ≃ₜ X)
    {L : ℝ} (hL : 0 < L) {D : Set (Space φ L)}
    (hD : IsOpen D) (hc : IsConnected D)
    (hfront : FiberSaturated (proj φ L ⁻¹' frontier D))
    (hf : (frontier (closure D)).Nonempty) :
    Nonempty (↥(closure D) ≃ₜ (X × Icc (0 : ℝ) 1)) := by
  obtain ⟨a, b, hab, hw, _, hcl⟩ := region_short_strip φ hL hD hc hfront hf
  exact ⟨(Homeomorph.setCongr hcl).trans
    ((closedStripHomeomorphImage φ hL hw).symm.trans (closedCylinderUnitHomeomorph hab))⟩

/-- The regular-open condition states exactly which topological boundary
conversion is being used; it is not identified with a smooth boundary by fiat. -/
theorem frontier_closure_eq_of_regularOpen {Z : Type*} [TopologicalSpace Z]
    {D : Set Z} (hD : IsOpen D) (hregular : D = interior (closure D)) :
    frontier (closure D) = frontier D := by
  simp only [frontier, closure_closure, ← hregular, hD.interior_eq]

/-- Sphere-quotient version with the blueprint's twist convention.
Regularity remains an explicit topological assumption. No smooth structure,
arbitrary sphere-bundle identification or diffeomorphism is claimed. -/
theorem sphere_bundle_quotient_regular_region (φ : Sphere2 ≃ₜ Sphere2)
    {L : ℝ} (hL : 0 < L) {D : Set (Space φ.symm L)}
    (hD : IsOpen D) (hc : IsConnected D)
    (hregular : D = interior (closure D))
    (hfront : FiberSaturated (proj φ.symm L ⁻¹' frontier D))
    (hne : (frontier D).Nonempty) :
    Nonempty (↥(closure D) ≃ₜ (Sphere2 × Icc (0 : ℝ) 1)) := by
  apply region_closure_homeomorph φ.symm hL hD hc hfront
  rwa [frontier_closure_eq_of_regularOpen hD hregular]

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
