import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.InteriorModel

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Smooth models at boundary points suffice: interior models are constructed, not assumed. -/
theorem exists_smoothClosedDomain_of_boundary_models
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace E N]
    [IsManifold (𝓘(ℝ, E)) ∞ N] (I : ModelWithCorners ℝ E H)
    {K : Set N} (hK : IsClosed K)
    (hboundary : ∀ y ∈ frontier K, ∃ e : OpenPartialHomeomorph N E,
      y ∈ e.source ∧ e ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N ∧ e.IsImage K (range I)) :
    ∃ cs : ChartedSpace H K,
      letI : ChartedSpace H K := cs
      IsManifold I ∞ K ∧ IsSmoothEmbedding I (𝓘(ℝ, E)) ∞ (Subtype.val : K → N) ∧
      HasAmbientModelCharts I K ∧ (Subtype.val : K → N) '' I.boundary K = frontier K :=
/- SWARM_PROOF_BEGIN -/
by
  refine DomainAtlas.exists_smoothClosedDomain_structure (I := I) hK ?_
  intro p
  by_cases hp : p.val ∈ interior K
  · exact interior_point_has_ambient_model I hp
  · have hpF : p.val ∈ frontier K := by
      rw [hK.frontier_eq]
      exact ⟨p.property, hp⟩
    exact hboundary p.val hpF
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
