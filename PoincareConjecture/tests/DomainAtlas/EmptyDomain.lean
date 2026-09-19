import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.ClosedDomain
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Empty domains do not require an accidental global Nonempty subtype assumption. -/
theorem empty_domain_structure_sanity {E H N : Type*}
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
