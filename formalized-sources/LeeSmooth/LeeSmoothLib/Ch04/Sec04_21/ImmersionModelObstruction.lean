import Mathlib.Geometry.Manifold.Immersion
import LeeSmoothLib.Ch01.Sec01_06.Theorem_1_46

open scoped Manifold ContDiff Topology
open Set Manifold

namespace ImmersionModelObstruction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {f : M → N} {p : M}

/-- The zero-tail immersion normal form from a zero-dimensional model into an actual
interior point forces zero to be an interior point of the target model range. -/
theorem zero_mem_interior_range_of_immersion
    (hf : IsImmersionAt I J ∞ f p) (hp : J.IsInteriorPoint (f p)) :
    (0 : F) ∈ interior (range J) := by
  have hpDom : p ∈ (hf.domChart.extend I).source := by
    simpa only [OpenPartialHomeomorph.extend_source] using hf.mem_domChart_source
  have hcoord := hf.writtenInCharts ((hf.domChart.extend I).map_source hpDom)
  simp only [Function.comp_apply, (hf.domChart.extend I).left_inv hpDom] at hcoord
  have hz : hf.domChart.extend I p = 0 := Subsingleton.elim _ _
  have hcodZero : hf.codChart.extend J (f p) = 0 := by
    rw [hz] at hcoord
    exact hcoord.trans (map_zero hf.equiv)
  have hint : hf.codChart.extend J (f p) ∈ interior (hf.codChart.extend J).target :=
    (J.isInteriorPoint_iff_of_mem_maximalAtlas (by simp)
      hf.codChart_mem_maximalAtlas hf.mem_codChart_source).mp hp
  have hrange : hf.codChart.extend J (f p) ∈ interior (range J) :=
    interior_mono (hf.codChart.extend_target_subset_range (I := J)) hint
  rwa [hcodZero] at hrange

/-- A boundaryless manifold condition on the actual target points cannot replace a
model-range condition in the zero-tail immersion definition. -/
theorem not_immersion_of_zero_notMem_interior_range
    (hzero : (0 : F) ∉ interior (range J)) (hp : J.IsInteriorPoint (f p)) :
    ¬ IsImmersionAt I J ∞ f p :=
  fun hf ↦ hzero (zero_mem_interior_range_of_immersion hf hp)

end ImmersionModelObstruction
