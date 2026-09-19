import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.Core
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N]
  {I : ModelWithCorners ℝ E H} {K : Set N}

/-- Smooth ambient maximal-atlas charts have the required ordinary transition. -/
theorem ambient_chart_transition_contDiffOn [ChartedSpace E N]
    [IsManifold (𝓘(ℝ, E)) ∞ N] (e e' : OpenPartialHomeomorph N E)
    (he : e ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N)
    (he' : e' ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N) :
    ContDiffOn ℝ ∞ (e' ∘ e.symm) (e.symm.trans e').source :=
/- SWARM_PROOF_BEGIN -/
by
  have h := (IsManifold.compatible_of_mem_maximalAtlas he he').1
  simpa [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, preimage_id_eq, id_eq, inter_univ, OpenPartialHomeomorph.coe_trans] using h
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
