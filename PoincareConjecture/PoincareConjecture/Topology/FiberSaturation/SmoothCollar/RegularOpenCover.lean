import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Restriction
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.CollarClosureFrontier

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Full smooth collars covering the actual frontier force regular openness of the complement. -/
theorem smoothCollar_cover_regularOpen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace V X] [ChartedSpace (V × ℝ) N]
    [IsManifold (𝓘(ℝ, V)) ∞ X] [IsManifold (𝓘(ℝ, V × ℝ)) ∞ N] [PreconnectedSpace X] [LocallyConnectedSpace N]
    {C : Set N} (hC : IsClosed C) {p : N}
    (hcover : ∀ y ∈ frontier (connectedComponentIn Cᶜ p),
      ∃ Φ : PartialDiffeomorph ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ)))
          (𝓘(ℝ, V × ℝ)) (X × ℝ) N ∞,
        Φ.source = (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1 ∧
        (∀ z ∈ Φ.source, Φ z ∈ C ↔ z.2 ≤ 0) ∧ ∃ x : X, Φ (x, 0) = y) :
    frontier (closure (connectedComponentIn Cᶜ p)) = frontier (connectedComponentIn Cᶜ p) ∧
    connectedComponentIn Cᶜ p = interior (closure (connectedComponentIn Cᶜ p)) :=
/- SWARM_PROOF_BEGIN -/
by
  let D := connectedComponentIn Cᶜ p
  have hD : IsOpen D := hC.isOpen_compl.connectedComponentIn
  have hfront : frontier (closure D) = frontier D := by
    apply Subset.antisymm
    · exact frontier_closure_subset
    · intro y hy
      obtain ⟨Φ, hsource, hsideΦ, x, hxy⟩ := hcover y hy
      let F := Φ.toOpenPartialHomeomorph
      have hΦF (z : X × ℝ) : F z = Φ z := by
        rw [← OpenPartialHomeomorph.coe_toPartialEquiv F]
        rfl
      have hf : Topology.IsOpenEmbedding (collarRestriction F) :=
        (collarRestriction_isOpenEmbedding F hsource).1
      have hside : ∀ z, collarRestriction F z ∈ C ↔ (z.2 : ℝ) ≤ 0 := by
        intro z
        have hz : (z.1, (z.2 : ℝ)) ∈ Φ.source := by
          rw [hsource]
          exact ⟨mem_univ _, z.2.property⟩
        simpa [collarRestriction, hΦF] using hsideΦ _ hz
      have hcenter : collarRestriction F (x, neckCenter) = y := by
        change F (x, (neckCenter : ℝ)) = y
        rw [hΦF]
        exact hxy
      have hx : collarRestriction F (x, neckCenter) ∈ frontier D := by
        rwa [hcenter]
      have : collarRestriction F (x, neckCenter) ∈ frontier (closure D) :=
        DomainAtlas.oneSidedCollar_center_mem_frontier_closure hf hside hx x
      rwa [← hcenter]
  exact ⟨hfront, regularOpen_of_frontier_closure_eq hD hfront⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
