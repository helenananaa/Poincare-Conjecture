import Mathlib.Geometry.Manifold.SmoothEmbedding

open scoped Manifold ContDiff
open Set Function

namespace Manifold.SweepRestriction
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
variable {n : ℕ∞ω} [IsManifold I n M]

private lemma restricted_compatible
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M)
    {U : TopologicalSpace.Opens M} (hU : Nonempty U) :
    (e.subtypeRestr hU).symm ≫ₕ e'.subtypeRestr hU ∈ contDiffGroupoid n I :=
  (contDiffGroupoid n I).mem_of_eqOnSource
    (closedUnderRestriction'
      ((contDiffGroupoid n I).compatible_of_mem_maximalAtlas he he')
      (e.isOpen_inter_preimage_symm U.2))
    (e.subtypeRestr_symm_trans_subtypeRestr hU e')

private lemma restricted_atlas {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M)
    {U : TopologicalSpace.Opens M} (hU : Nonempty U) :
    e.subtypeRestr hU ∈ IsManifold.maximalAtlas I n U := by
  intro e' he'
  obtain ⟨x, hx⟩ := TopologicalSpace.Opens.chart_eq hU he'
  rw [hx]
  exact ⟨restricted_compatible he
      (IsManifold.subset_maximalAtlas (chart_mem_atlas H (x : M))) hU,
    restricted_compatible
      (IsManifold.subset_maximalAtlas (chart_mem_atlas H (x : M))) he hU⟩

/-- Restriction to an open submanifold preserves immersion, including at boundary points. -/
theorem isImmersion_comp_subtype {f : M → N} (hf : IsImmersion I J n f)
    (U : TopologicalSpace.Opens M) :
    IsImmersion I J n (f ∘ (Subtype.val : U → M)) := by
  refine ⟨hf.complement, inferInstance, inferInstance, ?_⟩
  intro q
  let h := hf.isImmersionOfComplement_complement (q : M)
  have hU : Nonempty U := ⟨q⟩
  refine IsImmersionAtOfComplement.mk_of_charts h.equiv
    (h.domChart.subtypeRestr hU) h.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using h.mem_domChart_source
  · exact h.mem_codChart_source
  · exact restricted_atlas h.domChart_mem_maximalAtlas hU
  · exact h.codChart_mem_maximalAtlas
  · intro x hx
    exact h.source_subset_preimage_source (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hx)
  · intro y hy
    rw [OpenPartialHomeomorph.extend_target] at hy
    have hyDom : I.symm y ∈ h.domChart.target :=
      h.domChart.subtypeRestr_target_subset hU hy.1
    have hyTarget : y ∈ (h.domChart.extend I).target := by
      rw [OpenPartialHomeomorph.extend_target]
      exact ⟨hyDom, hy.2⟩
    have hval := h.domChart.subtypeRestr_symm_apply (U := U) hU hy.1
    have heq := h.writtenInCharts hyTarget
    dsimp only [Function.comp_apply] at hval
    simpa only [Function.comp_apply, OpenPartialHomeomorph.extend_coe_symm, hval] using heq

end Manifold.SweepRestriction
