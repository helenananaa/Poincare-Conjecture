import PoincareConjecture.Topology.FiberSaturation.SmoothRelativeProduct
import PoincareConjecture.Topology.FiberSaturation.AbstractSmoothBundleRegion

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Manifold
open scoped Manifold ContDiff
variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] {I : ModelWithCorners ℝ V H}

/-- The open-product branch of boundary pairing, including every open real
interval and its genuine relative frontier. No ambient change of the closure's
smooth structure, unspecified embedding composition, or boundary premise is used. -/
theorem relative_sphere_region_boundary_pairing
    (J : TopologicalSpace.Opens ℝ) (hinterval : OrdConnected (J : Set ℝ))
    {D : Set (Sphere2 × J)} [ChartedSpace H (closure D)] [IsManifold I ∞ (closure D)]
    (hD : IsOpen D) (hc : IsConnected D) (hs : FiberSaturated (frontier D))
    (hk : IsCompact (closure D))
    (hf : IsSmoothEmbedding I ((𝓡 2).prod 𝓘(ℝ,ℝ)) ∞
      (Subtype.val : closure D → Sphere2 × J)) :
    Nonempty (↥(closure D) ≃ₘ⟮I,(𝓡 2).prod (𝓡∂ 1)⟯ (Sphere2 × Icc (0 : ℝ) 1)) ∧
    ∃ a b : J, (a : ℝ) < b ∧
      frontier D = (univ : Set Sphere2) ×ˢ ({a,b} : Set J) ∧
      Disjoint ((univ : Set Sphere2) ×ˢ ({a} : Set J)) (univ ×ˢ ({b} : Set J)) ∧
      (∀ x : Sphere2, connectedComponentIn (frontier D) (x,a) = univ ×ˢ ({a} : Set J)) ∧
      (∀ x : Sphere2, connectedComponentIn (frontier D) (x,b) = univ ×ˢ ({b} : Set J)) ∧
      (∀ z ∈ frontier D, connectedComponentIn (frontier D) z = univ ×ˢ ({a} : Set J) ∨
        connectedComponentIn (frontier D) z = univ ×ˢ ({b} : Set J)) :=
  ⟨relative_product_region_diffeomorph J hinterval hD hc hs hk hf,
    sphere_product_two_frontier_components J.isOpen hD hc hs hk⟩

end PoincareConjecture.Topology.FiberSaturation
