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

/-- The constructed chart family satisfies the existing ambient-model API. -/
theorem domainCharted_hasAmbientModelCharts (c : K → ModelDomainChart I K)
    (hc : ∀ p, p ∈ (c p).intrinsic.source) :
    letI : ChartedSpace H K := domainChartedSpace c hc
    HasAmbientModelCharts I K :=
/- SWARM_PROOF_BEGIN -/
by
  intro p
  refine ⟨(c p).ambient, ?_, (c p).model_image, ?_⟩
  · have hp := hc p
    rwa [(c p).source_eq] at hp
  · exact ((c p).forward_eq p (hc p)).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
