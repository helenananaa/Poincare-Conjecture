import PoincareConjecture.Topology.FiberSaturation.SmoothDomainRegularity
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Manifold
open scoped Manifold ContDiff

/-- The canonical model inclusion is a genuinely C-infinity smooth embedding.
This provides non-vacuous boundary-bearing instances of the new hypotheses. -/
theorem model_inclusion_smoothEmbedding {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) : IsSmoothEmbedding I 𝓘(ℝ, E) ∞ I := by
  refine ⟨⟨PUnit, inferInstance, inferInstance, ?_⟩, I.isClosedEmbedding.isEmbedding⟩
  intro x
  apply IsImmersionAtOfComplement.mk_of_charts (ContinuousLinearEquiv.prodUnique ℝ E PUnit)
    (chartAt H x) (chartAt E (I x)) (mem_chart_source H x) (mem_chart_source E (I x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (I x))
  · simp
  · intro y hy
    have hr : y ∈ range I := by
      simpa [OpenPartialHomeomorph.extend_target, chartAt_self_eq] using hy
    simpa [chartAt_self_eq] using (I.right_inv hr)

end PoincareConjecture.Topology.FiberSaturation
