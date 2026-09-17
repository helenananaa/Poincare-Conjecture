import PoincareConjecture.Topology.FiberSaturation.Components
import PoincareConjecture.Topology.FiberSaturation.Embedding
import PoincareConjecture.Topology.FiberSaturation.Sphere

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {a b : ℝ}

/-- Restrict a closed collar map to its open parameter interval. -/
def collarInteriorMap (f : X × Icc a b → Y) : X × Ioo a b → Y :=
  f ∘ Prod.map id (Set.inclusion Ioo_subset_Icc_self)

/-- Restricting collar coordinates preserves continuity. -/
theorem continuous_collarInteriorMap {f : X × Icc a b → Y} (hf : Continuous f) :
    Continuous (collarInteriorMap f) :=
  hf.comp (continuous_id.prodMap (continuous_inclusion Ioo_subset_Icc_self))

/-- Restricting an actual collar embedding preserves its embedding property. -/
theorem isEmbedding_collarInteriorMap {f : X × Icc a b → Y}
    (hf : Topology.IsEmbedding f) : Topology.IsEmbedding (collarInteriorMap f) :=
  hf.comp (Topology.IsEmbedding.id.prodMap (Topology.IsEmbedding.inclusion Ioo_subset_Icc_self))

omit [TopologicalSpace X] in
/-- Ambient frontier saturation restricts from the closed to the open collar. -/
theorem collarInterior_frontierSaturated {f : X × Icc a b → Y} {D : Set Y}
    (hfront : FiberSaturated (f ⁻¹' frontier D)) :
    FiberSaturated (collarInteriorMap f ⁻¹' frontier D) := by
  intro x₁ x₂ t h
  exact hfront h

/-- The open-collar component interval and its actual saturated frontier are
both derived from ambient boundary control, not taken as hypotheses. -/
theorem collar_component_interval [PreconnectedSpace X]
    {f : X × Icc a b → Y} (hf : Continuous f) {D : Set Y} (hD : IsOpen D)
    (hfront : FiberSaturated (f ⁻¹' frontier D))
    {p : X × Ioo a b} (hp : collarInteriorMap f p ∈ D) :
    (∃ A : Set ℝ, IsOpen A ∧ OrdConnected A ∧ A.Nonempty ∧ A ⊆ Ioo a b ∧
      connectedComponentIn (collarInteriorMap f ⁻¹' D) p =
        univ ×ˢ ((Subtype.val : Ioo a b → ℝ) ⁻¹' A)) ∧
    FiberSaturated (frontier (connectedComponentIn (collarInteriorMap f ⁻¹' D) p)) := by
  have hc := continuous_collarInteriorMap hf
  have hs := preimage_fiberSaturated_of_ambient_frontier hc hD
    (collarInterior_frontierSaturated hfront)
  exact ⟨component_open_interval isOpen_Ioo (hD.preimage hc) hs hp,
    frontier_component_fiberSaturated hs hp⟩

/-- Components in the real ambient intersection are images of the interval
cylinders. The collar coordinates are an embedding, not an assumed answer. -/
theorem embedded_collar_component_interval [PreconnectedSpace X]
    {f : X × Icc a b → Y} (hf : Topology.IsEmbedding f) {D : Set Y} (hD : IsOpen D)
    (hfront : FiberSaturated (f ⁻¹' frontier D))
    {p : X × Ioo a b} (hp : collarInteriorMap f p ∈ D) :
    ∃ A : Set ℝ, IsOpen A ∧ OrdConnected A ∧ A.Nonempty ∧ A ⊆ Ioo a b ∧
      connectedComponentIn (D ∩ range (collarInteriorMap f)) (collarInteriorMap f p) =
        collarInteriorMap f '' (univ ×ˢ ((Subtype.val : Ioo a b → ℝ) ⁻¹' A)) := by
  obtain ⟨⟨A, ho, hc, hn, hsub, heq⟩, _⟩ :=
    collar_component_interval hf.continuous hD hfront hp
  refine ⟨A, ho, hc, hn, hsub, ?_⟩
  rw [← image_preimage_eq_inter_range,
    ← embedding_image_connectedComponentIn (isEmbedding_collarInteriorMap hf) hp, heq]

/-- Coordinate-explicit topological content of the closed-collar node.
The displayed-frontier condition concerns the original ambient frontier.
All parameter fibers, including endpoints, satisfy the three-way alternative. -/
theorem sphere_closed_collar_saturation {f : Sphere2 × Icc a b → Y}
    (hf : Topology.IsEmbedding f) {D : Set Y} (hD : IsOpen D)
    (hdisplay : ∃ T : Set (Icc a b), f ⁻¹' frontier D = univ ×ˢ T)
    {p : Sphere2 × Ioo a b} (hp : collarInteriorMap f p ∈ D) :
    (∃ A : Set ℝ, IsOpen A ∧ OrdConnected A ∧ A.Nonempty ∧ A ⊆ Ioo a b ∧
      connectedComponentIn (D ∩ range (collarInteriorMap f)) (collarInteriorMap f p) =
        collarInteriorMap f '' (univ ×ˢ ((Subtype.val : Ioo a b → ℝ) ⁻¹' A))) ∧
    (∀ t : Icc a b, (∀ x : Sphere2, f (x, t) ∈ D) ∨
      (∀ x : Sphere2, f (x, t) ∈ frontier D) ∨
      (∀ x : Sphere2, f (x, t) ∉ closure D)) ∧
    FiberSaturated (frontier (connectedComponentIn (collarInteriorMap f ⁻¹' D) p)) := by
  obtain ⟨T, hT⟩ := hdisplay
  have hfront : FiberSaturated (f ⁻¹' frontier D) := by
    rw [hT]
    exact fiberSaturated_univ_prod _
  exact ⟨embedded_collar_component_interval hf hD hfront hp,
    (fun t => ambient_fiber_trichotomy hf.continuous hD hfront p.1 t),
    (collar_component_interval hf.continuous hD hfront hp).2⟩

end PoincareConjecture.Topology.FiberSaturation
