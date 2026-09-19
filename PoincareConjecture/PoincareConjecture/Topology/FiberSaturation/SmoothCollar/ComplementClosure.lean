import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.BoundaryModel
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.RegularOpenCover
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.BoundaryToGlobal

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Construct the actual complementary closure as a smooth domain from a covering
of its frontier by genuine smooth one-sided full collars. No closure atlas or
ambient local-set-model assumption is supplied separately. -/
theorem exists_smoothClosure_of_smoothCollar_cover {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace V X] [ChartedSpace (V × ℝ) N]
    [IsManifold (𝓘(ℝ, V)) ∞ X] [IsManifold (𝓘(ℝ, V × ℝ)) ∞ N] [PreconnectedSpace X] [LocallyConnectedSpace N]
    {C : Set N} (hC : IsClosed C) {p : N}
    (hcover : ∀ y ∈ frontier (connectedComponentIn Cᶜ p),
      ∃ Φ : PartialDiffeomorph ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ)))
          (𝓘(ℝ, V × ℝ)) (X × ℝ) N ∞,
        Φ.source = (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1 ∧
        (∀ z ∈ Φ.source, Φ z ∈ C ↔ z.2 ≤ 0) ∧ ∃ x : X, Φ (x, 0) = y) :
    ∃ cs : ChartedSpace (HalfSpace V) (closure (connectedComponentIn Cᶜ p)),
      letI : ChartedSpace (HalfSpace V) (closure (connectedComponentIn Cᶜ p)) := cs
      IsManifold (halfSpaceModel V) ∞ (closure (connectedComponentIn Cᶜ p)) ∧
      IsSmoothEmbedding (halfSpaceModel V) (𝓘(ℝ, V × ℝ)) ∞
        (Subtype.val : closure (connectedComponentIn Cᶜ p) → N) ∧
      (Subtype.val : closure (connectedComponentIn Cᶜ p) → N) ''
        (halfSpaceModel V).boundary (closure (connectedComponentIn Cᶜ p)) =
          frontier (connectedComponentIn Cᶜ p) ∧
      connectedComponentIn Cᶜ p = interior (closure (connectedComponentIn Cᶜ p)) :=
/- SWARM_PROOF_BEGIN -/
by
  let D := connectedComponentIn Cᶜ p
  obtain ⟨hfront, hreg⟩ := smoothCollar_cover_regularOpen hC hcover
  have hK : IsClosed (closure D) := isClosed_closure
  have hboundary : ∀ y ∈ frontier (closure D),
      ∃ e : OpenPartialHomeomorph N (V × ℝ),
        y ∈ e.source ∧
        e ∈ IsManifold.maximalAtlas (𝓘(ℝ, V × ℝ)) ∞ N ∧
        e.IsImage (closure D) (range (halfSpaceModel V)) := by
    intro y hy
    have hyD : y ∈ frontier D := by
      rwa [hfront] at hy
    obtain ⟨Φ, hsource, hside, x, hxy⟩ := hcover y hyD
    have hx : Φ (x, 0) ∈ frontier D := by
      rwa [hxy]
    obtain ⟨e, he_src, he_atlas, he_image⟩ :=
      smoothCollar_center_has_ambient_model Φ hsource hside hx
    refine ⟨e, ?_, he_atlas, he_image⟩
    rwa [hxy] at he_src
  obtain ⟨cs, hman, hembed, _, hbdry⟩ :=
    exists_smoothClosedDomain_of_boundary_models (halfSpaceModel V) hK hboundary
  refine ⟨cs, hman, hembed, ?_, hreg⟩
  rwa [hfront] at hbdry
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
