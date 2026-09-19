import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.Core
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.ManifoldFamily
import PoincareConjecture.Topology.FiberSaturation.SmoothEmbeddingModels
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N]
  {I : ModelWithCorners ℝ E H} {K : Set N}

/-- The inclusion of a constructed smooth domain is genuinely a smooth embedding. -/
theorem domainCharted_inclusion_smoothEmbedding [ChartedSpace E N]
    [IsManifold (𝓘(ℝ, E)) ∞ N] (c : K → ModelDomainChart I K)
    (hc : ∀ p, p ∈ (c p).intrinsic.source)
    (hca : ∀ p, (c p).ambient ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N) :
    letI : ChartedSpace H K := domainChartedSpace c hc
    IsSmoothEmbedding I (𝓘(ℝ, E)) ∞ (Subtype.val : K → N) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : ChartedSpace H K := domainChartedSpace c hc
  letI : IsManifold I ∞ K := domainCharted_isManifold c hc hca
  refine ⟨⟨PUnit, inferInstance, inferInstance, ?_⟩, .subtypeVal⟩
  intro p
  apply IsImmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.prodUnique ℝ E PUnit)
    (c p).intrinsic (c p).ambient (hc p)
  · have hp := hc p
    rwa [(c p).source_eq] at hp
  · exact IsManifold.subset_maximalAtlas (mem_range_self p)
  · exact hca p
  · rw [(c p).source_eq]
  · intro y hy
    rw [OpenPartialHomeomorph.extend_target] at hy
    have hIt : I.symm y ∈ (c p).intrinsic.target := hy.1
    have hr : y ∈ range I := hy.2
    have hval := (c p).inverse_eq (I.symm y) hIt
    rw [I.right_inv hr] at hval
    have hyA : y ∈ (c p).ambient.target := by
      have : I.symm y ∈ I ⁻¹' (c p).ambient.target := by
        rwa [(c p).target_eq] at hIt
      simpa [mem_preimage, I.right_inv hr] using this
    simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe, id_eq,
      ContinuousLinearEquiv.prodUnique_apply]
    rw [hval]
    exact (c p).ambient.right_inv hyA
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
