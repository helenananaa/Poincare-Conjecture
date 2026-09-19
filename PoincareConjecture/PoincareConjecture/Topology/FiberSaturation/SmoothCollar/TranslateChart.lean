import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Translation of ambient coordinates preserves the original smooth atlas. -/
theorem translated_chart_mem_maximalAtlas
    {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace N] [ChartedSpace E N] [IsManifold (𝓘(ℝ, E)) ∞ N]
    (a : OpenPartialHomeomorph N E)
    (ha : a ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N) (v : E) :
    a.trans (Homeomorph.addRight v).toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N :=
/- SWARM_PROOF_BEGIN -/
by
  let τ := (Homeomorph.addRight v).toOpenPartialHomeomorph
  have hτ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ τ := by
    apply ContDiff.contMDiff
    change ContDiff ℝ ∞ fun x : E => x + v
    fun_prop
  have hτsymm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ τ.symm := by
    apply ContDiff.contMDiff
    change ContDiff ℝ ∞ fun x : E => x + -v
    fun_prop
  refine (a.trans τ).mem_maximalAtlas_of_contMDiffOn ?_ ?_
  · rw [OpenPartialHomeomorph.trans_source]
    exact hτ.contMDiffOn.comp' (contMDiffOn_of_mem_maximalAtlas ha)
  · rw [OpenPartialHomeomorph.trans_target]
    exact (contMDiffOn_symm_of_mem_maximalAtlas ha).comp' hτsymm.contMDiffOn
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
