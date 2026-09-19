import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.ProductChartSmooth

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Actual smooth collar coordinates belong to the ambient smooth maximal atlas. -/
theorem collarCoordinates_mem_maximalAtlas {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace V X] [ChartedSpace (V × ℝ) N]
    [IsManifold (𝓘(ℝ, V)) ∞ X] [IsManifold (𝓘(ℝ, V × ℝ)) ∞ N]
    (Φ : PartialDiffeomorph ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, V × ℝ)) (X × ℝ) N ∞)
    (a : OpenPartialHomeomorph X V)
    (ha : a ∈ IsManifold.maximalAtlas (𝓘(ℝ, V)) ∞ X) :
    collarCoordinates Φ.toOpenPartialHomeomorph a ∈
      IsManifold.maximalAtlas (𝓘(ℝ, V × ℝ)) ∞ N :=
/- SWARM_PROOF_BEGIN -/
by
  let F := Φ.toOpenPartialHomeomorph
  let b := a.prod (Homeomorph.refl ℝ).toOpenPartialHomeomorph
  have hb := product_chart_contMDiffOn a ha
  refine (F.symm.trans b).mem_maximalAtlas_of_contMDiffOn ?fwd ?inv
  · rw [OpenPartialHomeomorph.trans_source]
    refine hb.1.comp (Φ.contMDiffOn_invFun.mono inter_subset_left) ?_
    exact (mapsTo_preimage F.symm b.source).mono_left inter_subset_right
  · rw [OpenPartialHomeomorph.trans_target]
    refine Φ.contMDiffOn_toFun.comp (hb.2.mono inter_subset_left) ?_
    exact (mapsTo_preimage b.symm F.symm.target).mono_left inter_subset_right
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
