import Mathlib.Geometry.Manifold.Instances.Real
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.ClosedDomain
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Nonvacuity regression: a genuine model range satisfies the construction theorem. -/
theorem domainAtlasSanity_modelRange {E H : Type*}
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

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Empty domains do not require an accidental global Nonempty subtype assumption. -/
theorem domainAtlasSanity_empty {E H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace N] [ChartedSpace E N] [IsManifold (𝓘(ℝ, E)) ∞ N]
    (I : ModelWithCorners ℝ E H) :
    ∃ cs : ChartedSpace H (∅ : Set N),
      letI : ChartedSpace H (∅ : Set N) := cs
      IsManifold I ∞ (∅ : Set N) ∧
      IsSmoothEmbedding I (𝓘(ℝ, E)) ∞ (Subtype.val : (∅ : Set N) → N) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨cs, hM, hE, -, -⟩ :=
    exists_smoothClosedDomain_structure (I := I) (K := (∅ : Set N))
      isClosed_empty (fun p : (∅ : Set N) => p.2.elim)
  exact ⟨cs, hM, hE⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas

open Set
open scoped Manifold ContDiff
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
/-- A concrete boundary-bearing three-dimensional model checks nonvacuity. -/
example : ∃ cs : ChartedSpace (EuclideanHalfSpace 3) (range (𝓡∂ 3)),
    letI : ChartedSpace (EuclideanHalfSpace 3) (range (𝓡∂ 3)) := cs
    IsManifold (𝓡∂ 3) ∞ (range (𝓡∂ 3)) := by
  obtain ⟨cs, hmanifold, _⟩ := domainAtlasSanity_modelRange (𝓡∂ 3)
  exact ⟨cs, hmanifold⟩
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
