import PoincareConjecture.Topology.FiberSaturation.ClosedCollar

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- An open component of an open set can have frontier only on the frontier
of the original set. Closedness is proved in the original set's subspace. -/
theorem frontier_componentIn_subset {Z : Type*} [TopologicalSpace Z]
    {U : Set Z} (hU : IsOpen U) {p : Z} (hp : p ∈ U)
    (hC : IsOpen (connectedComponentIn U p)) :
    frontier (connectedComponentIn U p) ⊆ frontier U := by
  intro z hz
  rw [hC.frontier_eq] at hz
  rw [hU.frontier_eq]
  refine ⟨closure_mono (connectedComponentIn_subset U p) hz.1, ?_⟩
  intro hzU
  have hclosed := (Topology.IsInducing.subtypeVal.isClosed_iff').mp
    (isClosed_connectedComponent (x := (⟨p, hp⟩ : U)))
  have hzc : (⟨z, hzU⟩ : U) ∈ connectedComponent (⟨p, hp⟩ : U) := by
    apply hclosed ⟨z, hzU⟩
    simpa only [connectedComponentIn_eq_image hp] using hz.1
  apply hz.2
  rw [connectedComponentIn_eq_image hp]
  exact ⟨⟨z, hzU⟩, hzc, rfl⟩

/-- The actual relative frontier of a collar-intersection component maps
into the original ambient frontier. The component-frontier assumption from
an informal proof is discharged here, rather than retained as an input. -/
theorem collar_component_frontier_subset_ambient
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace Y]
    {a b : ℝ} {f : X × Icc a b → Y} (hf : Continuous f) {D : Set Y} (hD : IsOpen D)
    (hfront : FiberSaturated (f ⁻¹' frontier D))
    {p : X × Ioo a b} (hp : collarInteriorMap f p ∈ D) :
    frontier (connectedComponentIn (collarInteriorMap f ⁻¹' D) p) ⊆
      collarInteriorMap f ⁻¹' frontier D := by
  have hc := continuous_collarInteriorMap hf
  obtain ⟨⟨A, ho, _, _, _, heq⟩, _⟩ := collar_component_interval hf hD hfront hp
  have hC : IsOpen (connectedComponentIn (collarInteriorMap f ⁻¹' D) p) := by
    rw [heq]
    exact isOpen_univ.prod (ho.preimage continuous_subtype_val)
  exact (frontier_componentIn_subset (hD.preimage hc) hp hC).trans
    (hc.frontier_preimage_subset D)

end PoincareConjecture.Topology.FiberSaturation
