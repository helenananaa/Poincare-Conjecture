import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.OrientedCollar
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.ImageCut
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- A cover of the actual continuing frontier by finite oriented neck cuts
constructs the smooth structure of any exterior component's actual closure. -/
theorem exists_smoothClosure_of_finite_neck_cut_cover
    {V X N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace V X] [ChartedSpace (V × ℝ) N]
    [IsManifold (𝓘(ℝ,V)) ∞ X] [IsManifold (𝓘(ℝ,V × ℝ)) ∞ N]
    [PreconnectedSpace X] [LocallyConnectedSpace N]
    {C : Set N} (hC : IsClosed C) {p : N} (hp : p ∉ C)
    (hcover : ∀ y ∈ frontier C,
      ∃ Ψ : PartialDiffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) (𝓘(ℝ,V × ℝ)) (X × ℝ) N ∞,
      ∃ a b c s : ℝ, a < c ∧ c < b ∧ (s = 1 ∨ s = -1) ∧
        Ψ.source = (univ : Set X) ×ˢ Ioo a b ∧
        C ∩ Ψ.target = Ψ '' (Ψ.source ∩ {z | s*(z.2-c) ≤ 0}) ∧
        ∃ x : X, Ψ (x,c) = y) :
    ∃ cs : ChartedSpace (SmoothCollar.HalfSpace V) (closure (connectedComponentIn Cᶜ p)),
      letI : ChartedSpace (SmoothCollar.HalfSpace V) (closure (connectedComponentIn Cᶜ p)) := cs
      IsManifold (SmoothCollar.halfSpaceModel V) ∞ (closure (connectedComponentIn Cᶜ p)) ∧
      IsSmoothEmbedding (SmoothCollar.halfSpaceModel V) (𝓘(ℝ,V × ℝ)) ∞
        (Subtype.val : closure (connectedComponentIn Cᶜ p) → N) ∧
      (Subtype.val : closure (connectedComponentIn Cᶜ p) → N) ''
        (SmoothCollar.halfSpaceModel V).boundary (closure (connectedComponentIn Cᶜ p)) =
          frontier (connectedComponentIn Cᶜ p) ∧
      connectedComponentIn Cᶜ p = interior (closure (connectedComponentIn Cᶜ p)) :=
/- SWARM_PROOF_BEGIN -/
by
  have hfront : frontier (connectedComponentIn Cᶜ p) ⊆ frontier C :=
    complementary_component_frontier_subset hC hp
  refine SmoothCollar.exists_smoothClosure_of_smoothCollar_cover (X := X) (p := p) hC ?cover
  intro y hy
  have hyC : y ∈ frontier C := hfront hy
  obtain ⟨Ψ, a, b, c, s, hac, hcb, hs, hsource, hcut, x, hxy⟩ := hcover y hyC
  have hcut' := neck_cut_membership_of_image Ψ C c s hcut
  obtain ⟨Φ, hΦsrc, hΦside, hΦzero⟩ :=
    exists_smoothCollar_of_oriented_neck Ψ C a b c s hac hcb hs hsource hcut'
  refine ⟨Φ, hΦsrc, hΦside, x, ?_⟩
  rw [hΦzero]
  exact hxy
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
