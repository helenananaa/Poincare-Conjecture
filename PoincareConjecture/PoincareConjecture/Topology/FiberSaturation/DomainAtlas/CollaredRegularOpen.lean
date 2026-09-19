import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.Core
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.CollarClosureFrontier
import PoincareConjecture.Topology.FiberSaturation.Sphere
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N]
  {I : ModelWithCorners ℝ E H} {K : Set N}

/-- Covering the frontier by genuine one-sided sphere collars derives regular openness. -/
theorem complementary_regularOpen_of_sphereCollars
    {Y : Type*} [TopologicalSpace Y] [LocallyConnectedSpace Y]
    {C : Set Y} (hC : IsClosed C) {p : Y} (hp : p ∉ C)
    (hcover : ∀ y ∈ frontier (connectedComponentIn Cᶜ p),
      ∃ f : Sphere2 × NeckParameter → Y,
        Topology.IsOpenEmbedding f ∧
        (∀ z, f z ∈ C ↔ (z.2 : ℝ) ≤ 0) ∧
        ∃ x : Sphere2, f (x, neckCenter) = y) :
    connectedComponentIn Cᶜ p = interior (closure (connectedComponentIn Cᶜ p)) ∧
    frontier (closure (connectedComponentIn Cᶜ p)) =
      frontier (connectedComponentIn Cᶜ p) :=
/- SWARM_PROOF_BEGIN -/
by
  let D := connectedComponentIn Cᶜ p
  have hD : IsOpen D := hC.isOpen_compl.connectedComponentIn
  have hfront : frontier (closure D) = frontier D := by
    apply Subset.antisymm
    · exact frontier_closure_subset
    · intro y hy
      obtain ⟨f, hf, hside, x, hxy⟩ := hcover y hy
      have hx : f (x, neckCenter) ∈ frontier D := by rwa [hxy]
      have hy' : f (x, neckCenter) ∈ frontier (closure D) :=
        oneSidedCollar_center_mem_frontier_closure hf hside hx x
      rwa [← hxy]
  exact ⟨regularOpen_of_frontier_closure_eq hD hfront, hfront⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
