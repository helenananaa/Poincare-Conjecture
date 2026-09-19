import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.Core
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.AmbientSmooth
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.TransitionSmooth
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N]
  {I : ModelWithCorners ℝ E H} {K : Set N}

/-- A covering family of genuine restricted ambient smooth charts defines a manifold. -/
theorem domainCharted_isManifold [ChartedSpace E N]
    [IsManifold (𝓘(ℝ, E)) ∞ N] (c : K → ModelDomainChart I K)
    (hc : ∀ p, p ∈ (c p).intrinsic.source)
    (hca : ∀ p, (c p).ambient ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N) :
    letI : ChartedSpace H K := domainChartedSpace c hc
    IsManifold I ∞ K :=
/- SWARM_PROOF_BEGIN -/
by
  letI : ChartedSpace H K := domainChartedSpace c hc
  apply isManifold_of_contDiffOn I ∞ K
  rintro e e' ⟨p, rfl⟩ ⟨q, rfl⟩
  exact restricted_transition_contDiffOn (c p) (c q)
    (ambient_chart_transition_contDiffOn (c p).ambient (c q).ambient (hca p) (hca q))
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
