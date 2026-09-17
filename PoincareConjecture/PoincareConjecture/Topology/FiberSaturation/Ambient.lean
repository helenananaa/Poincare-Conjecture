import PoincareConjecture.Topology.FiberSaturation.Basic

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

variable {X B Y : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [TopologicalSpace Y] [PreconnectedSpace X]

/-- Ambient frontier control implies membership saturation after pullback.
The map need not be open, so the statement also applies at collar endpoints.
Crucially, no hypothesis is made about the frontier of the pulled-back set. -/
theorem preimage_fiberSaturated_of_ambient_frontier {f : X × B → Y}
    (hf : Continuous f) {D : Set Y} (hD : IsOpen D)
    (hfront : FiberSaturated (f ⁻¹' frontier D)) :
    FiberSaturated (f ⁻¹' D) := by
  intro x₁ x₂ t hx₁
  have hc : Continuous (fun x : X => f (x, t)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hs : IsPreconnected (range (fun x : X => f (x, t))) := by
    simpa only [image_univ] using isPreconnected_univ.image _ hc.continuousOn
  have hcl : closure D ∩ range (fun x : X => f (x, t)) ⊆ D := by
    rintro _ ⟨hz, x, rfl⟩
    by_contra hn
    have hb : f (x, t) ∈ frontier D := by
      rw [hD.frontier_eq]
      exact ⟨hz, hn⟩
    have hb₁ : f (x₁, t) ∈ frontier D := hfront hb
    rw [hD.frontier_eq] at hb₁
    exact hb₁.2 hx₁
  exact hs.subset_of_closure_inter_subset hD
    ⟨f (x₁, t), ⟨x₁, rfl⟩, hx₁⟩ hcl ⟨x₂, rfl⟩

/-- Every fiber is wholly inside the open region, wholly on its ambient
frontier, or wholly outside its ambient closure. Endpoints are included. -/
theorem ambient_fiber_trichotomy {f : X × B → Y} (hf : Continuous f)
    {D : Set Y} (hD : IsOpen D) (hfront : FiberSaturated (f ⁻¹' frontier D))
    (x₀ : X) (t : B) :
    (∀ x : X, f (x, t) ∈ D) ∨
    (∀ x : X, f (x, t) ∈ frontier D) ∨
    (∀ x : X, f (x, t) ∉ closure D) := by
  have hs := preimage_fiberSaturated_of_ambient_frontier hf hD hfront
  by_cases hin : f (x₀, t) ∈ D
  · exact Or.inl (fun _ => hs hin)
  by_cases hbd : f (x₀, t) ∈ frontier D
  · exact Or.inr (Or.inl (fun _ => hfront hbd))
  refine Or.inr (Or.inr (fun x hcl => ?_))
  have hn : f (x, t) ∉ D := fun h => hin (hs h)
  have hb : f (x, t) ∈ frontier D := by
    rw [hD.frontier_eq]
    exact ⟨hcl, hn⟩
  exact hbd (hfront hb)

end PoincareConjecture.Topology.FiberSaturation
