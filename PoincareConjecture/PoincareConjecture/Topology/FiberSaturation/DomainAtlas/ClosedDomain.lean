import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.Core
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.Restriction
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.ManifoldFamily
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.InclusionEmbedding
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.AmbientBridge
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N]
  {I : ModelWithCorners ℝ E H} {K : Set N}

/-- From ambient smooth local set models, construct the full smooth closed-domain
structure and identify its intrinsic boundary with its actual ambient frontier. -/
theorem exists_smoothClosedDomain_structure [ChartedSpace E N]
    [IsManifold (𝓘(ℝ, E)) ∞ N] (hK : IsClosed K)
    (hlocal : ∀ p : K, ∃ e : OpenPartialHomeomorph N E,
      p.1 ∈ e.source ∧
      e ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N ∧
      e.IsImage K (range I)) :
    ∃ cs : ChartedSpace H K,
      letI : ChartedSpace H K := cs
      IsManifold I ∞ K ∧
      IsSmoothEmbedding I (𝓘(ℝ, E)) ∞ (Subtype.val : K → N) ∧
      HasAmbientModelCharts I K ∧
      (Subtype.val : K → N) '' I.boundary K = frontier K :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  choose e he_src he_atlas he_image using hlocal
  have hchart : ∀ p : K, ∃ c : ModelDomainChart I K, c.ambient = e p :=
    fun p => exists_modelDomainChart I K (e p) (he_image p) p (he_src p)
  choose c hc_amb using hchart
  have hc : ∀ p, p ∈ (c p).intrinsic.source := by
    intro p
    rw [(c p).source_eq, hc_amb p]
    exact he_src p
  have hca : ∀ p, (c p).ambient ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N := by
    intro p
    rw [hc_amb p]
    exact he_atlas p
  refine ⟨domainChartedSpace c hc, ?_⟩
  letI : ChartedSpace H K := domainChartedSpace c hc
  refine ⟨domainCharted_isManifold c hc hca,
    domainCharted_inclusion_smoothEmbedding c hc hca,
    domainCharted_hasAmbientModelCharts c hc, ?_⟩
  exact intrinsicBoundary_image_eq (domainCharted_hasAmbientModelCharts c hc) hK
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
