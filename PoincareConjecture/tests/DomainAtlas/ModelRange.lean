import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.ClosedDomain
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Nonvacuity regression: a genuine model range satisfies the construction theorem. -/
theorem model_range_structure_sanity {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) :
    ∃ cs : ChartedSpace H (range I),
      letI : ChartedSpace H (range I) := cs
      IsManifold I ∞ (range I) ∧
      IsSmoothEmbedding I (𝓘(ℝ, E)) ∞ (Subtype.val : range I → E) ∧
      (Subtype.val : range I → E) '' I.boundary (range I) = frontier (range I) :=
/- SWARM_PROOF_BEGIN -/
by
  refine (exists_smoothClosedDomain_structure (N := E) (K := range I)
      I.isClosed_range ?_).imp fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩
  intro p
  refine ⟨OpenPartialHomeomorph.refl E, mem_univ p.1, ?_, ?_⟩
  · exact StructureGroupoid.id_mem_maximalAtlas (contDiffGroupoid ∞ 𝓘(ℝ, E))
  · intro x _
    exact Iff.rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
