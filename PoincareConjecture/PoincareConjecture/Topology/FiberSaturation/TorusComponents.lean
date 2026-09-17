import PoincareConjecture.Topology.FiberSaturation.TorusPeriod

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set
variable {X : Type*} [TopologicalSpace X]

/-- The inverse image of a quotient region is invariant under every deck iterate. -/
theorem deck_image_preimage (φ : X ≃ₜ X) (L : ℝ) (n : ℤ) (D : Set (Space φ L)) :
    (deck φ L n) '' (proj φ L ⁻¹' D) = proj φ L ⁻¹' D := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [mem_preimage, proj_deck] using hq
  · intro hp
    obtain ⟨q, rfl⟩ := (deck φ L n).surjective p
    exact ⟨q, by simpa only [mem_preimage, proj_deck] using hp, rfl⟩

/-- A nonempty finite-height open strip cannot equal its positive deck translate. -/
theorem openStrip_ne_deck_image [Nonempty X] (φ : X ≃ₜ X)
    {L a b : ℝ} (hL : 0 < L) (hab : a < b) :
    ((univ : Set X) ×ˢ Ioo a b) ≠ (deck φ L 1) '' ((univ : Set X) ×ˢ Ioo a b) := by
  intro heq
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨t, hat, ht⟩ := exists_between (lt_min hab (by linarith : a < a+L))
  have hmem : (x,t) ∈ (univ : Set X) ×ˢ Ioo a b :=
    ⟨mem_univ _, hat, lt_of_lt_of_le ht (min_le_left _ _)⟩
  rw [heq] at hmem
  obtain ⟨q, hq, hqt⟩ := hmem
  have htime : q.2 + L = t := by
    have htime' : q.2 + ((1 : ℤ) : ℝ) * L = t := congrArg Prod.snd hqt
    simpa using htime'
  have htL := lt_of_lt_of_le ht (min_le_right b (a+L))
  linarith [hq.2.1]

/-- Disjointness is derived from actual component maximality and finite strip
geometry. It is not added as an unproved input to this component theorem. -/
theorem lifted_strip_component_disjoint [Nonempty X] (φ : X ≃ₜ X)
    {L a b : ℝ} (hL : 0 < L) (D : Set (Space φ L)) {p : X × ℝ}
    (hp : p ∈ proj φ L ⁻¹' D)
    (hshape : connectedComponentIn (proj φ L ⁻¹' D) p = (univ : Set X) ×ˢ Ioo a b) :
    Disjoint ((univ : Set X) ×ˢ Ioo a b)
      ((deck φ L 1) '' ((univ : Set X) ×ˢ Ioo a b)) := by
  have hpoint : p ∈ (univ : Set X) ×ˢ Ioo a b := by
    rw [← hshape]
    exact mem_connectedComponentIn hp
  have hab : a < b := hpoint.2.1.trans hpoint.2.2
  have htranslate : (deck φ L 1) '' ((univ : Set X) ×ˢ Ioo a b) =
      connectedComponentIn (proj φ L ⁻¹' D) (deck φ L 1 p) := by
    rw [← hshape, (deck φ L 1).image_connectedComponentIn hp, deck_image_preimage]
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hz1 : z ∈ connectedComponentIn (proj φ L ⁻¹' D) p := by rwa [hshape]
  have hz2 : z ∈ connectedComponentIn (proj φ L ⁻¹' D) (deck φ L 1 p) :=
    by rwa [← htranslate]
  have heqC := (connectedComponentIn_eq hz1).trans (connectedComponentIn_eq hz2).symm
  rw [hshape, ← htranslate] at heqC
  exact openStrip_ne_deck_image φ hL hab heqC

/-- The strict period bound for a genuine lifted strip component. The only
remaining boundary input here is explicitly the nonempty frontier of its
image's closure; conversion from a smooth boundary remains a separate task. -/
theorem lifted_strip_component_width_lt [Nonempty X] (φ : X ≃ₜ X)
    {L a b : ℝ} (hL : 0 < L) (D : Set (Space φ L)) {p : X × ℝ}
    (hp : p ∈ proj φ L ⁻¹' D)
    (hshape : connectedComponentIn (proj φ L ⁻¹' D) p = (univ : Set X) ×ˢ Ioo a b)
    (hf : (frontier (closure (proj φ L '' ((univ : Set X) ×ˢ Ioo a b)))).Nonempty) :
    b-a < L :=
  width_lt_period_of_disjoint_frontier_closure φ hL
    (lifted_strip_component_disjoint φ hL D hp hshape) hf

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
