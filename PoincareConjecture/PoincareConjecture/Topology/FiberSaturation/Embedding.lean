import Mathlib.Topology.Connected.Basic

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An embedding carries the component in a set onto the component in its
image. This lets coordinate-space results describe actual ambient components. -/
theorem embedding_image_connectedComponentIn {f : X → Y} (hf : Topology.IsEmbedding f)
    {F : Set X} {x : X} (hx : x ∈ F) :
    f '' connectedComponentIn F x = connectedComponentIn (f '' F) (f x) := by
  apply Subset.antisymm (hf.continuous.image_connectedComponentIn_subset hx)
  let C := connectedComponentIn (f '' F) (f x)
  have hr : C ⊆ range f := by
    intro y hy
    obtain ⟨z, _, hz⟩ := connectedComponentIn_subset _ _ hy
    exact ⟨z, hz⟩
  have hc : IsPreconnected (f ⁻¹' C) := by
    apply hf.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset hr]
    exact isPreconnected_connectedComponentIn
  have hsub : f ⁻¹' C ⊆ F := by
    intro z hz
    obtain ⟨w, hw, heq⟩ := connectedComponentIn_subset _ _ hz
    exact hf.injective heq ▸ hw
  have hxC : x ∈ f ⁻¹' C := mem_connectedComponentIn ⟨x, hx, rfl⟩
  have hbound := hc.subset_connectedComponentIn hxC hsub
  intro y hy
  obtain ⟨z, rfl⟩ := hr hy
  exact ⟨z, hbound hy, rfl⟩

end PoincareConjecture.Topology.FiberSaturation
