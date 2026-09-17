import PoincareConjecture.Topology.FiberSaturation.EmbeddingLocalModel

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.Topology.FiberSaturation
open Set Function Manifold
open scoped Manifold ContDiff

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [J.Boundaryless]

/-- An equal-dimensional smooth embedding into a boundaryless model admits
exact ambient set charts, compatible with a chart in the source maximal atlas.
No boundary correspondence or extra ambient-chart hypothesis is assumed. -/
theorem exists_codimensionZero_ambient_chart {f : M → N}
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (x : M) :
    ∃ a : OpenPartialHomeomorph M H, ∃ e : OpenPartialHomeomorph N E,
      a ∈ IsManifold.maximalAtlas I ∞ M ∧ x ∈ a.source ∧
      f x ∈ e.source ∧ e.IsImage (range f) (range I) ∧ e (f x) = a.extend I x := by
  obtain ⟨C, hCgroup, hCspace, hC⟩ := hf.isImmersion
  letI := hCgroup
  letI := hCspace
  let h := hC x
  let k : C →ₗ[ℝ] F :=
    (h.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ E C)).toLinearMap
  have hkinj : Injective k := by
    intro u v huv
    exact congrArg Prod.snd (h.equiv.injective huv)
  letI : FiniteDimensional ℝ C := FiniteDimensional.of_injective k hkinj
  have hzero : Module.finrank ℝ C = 0 := by
    have heq := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, hdim] at heq
    omega
  letI : Subsingleton C := Module.finrank_zero_iff.mp hzero
  letI : Unique C := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  let l : F ≃L[ℝ] E := h.equiv.symm.trans (ContinuousLinearEquiv.prodUnique ℝ E C)
  let c : OpenPartialHomeomorph N F := {
    toPartialEquiv := h.codChart.extend J
    open_source := h.codChart.isOpen_extend_source
    open_target := h.codChart.isOpen_extend_target
    continuousOn_toFun := h.codChart.continuousOn_extend
    continuousOn_invFun := h.codChart.continuousOn_extend_symm }
  let e₀ := c.trans l.toHomeomorph.toOpenPartialHomeomorph
  have hmap : MapsTo f (h.domChart.extend I).source e₀.source := by
    intro y hy
    rw [h.domChart.extend_source] at hy
    change f y ∈ c.source ∩ c ⁻¹' univ
    exact ⟨by simpa [c, OpenPartialHomeomorph.extend_source] using
      h.source_subset_preimage_source hy, mem_univ _⟩
  have hcoord : EqOn (e₀ ∘ f) (h.domChart.extend I) (h.domChart.extend I).source := by
    intro y hy
    have hnormal := h.writtenInCharts ((h.domChart.extend I).map_source hy)
    simp only [comp_apply, (h.domChart.extend I).left_inv hy] at hnormal
    change l (h.codChart.extend J (f y)) = h.domChart.extend I y
    rw [hnormal]
    simp [l]
  have hx : x ∈ (h.domChart.extend I).source := by
    simpa [OpenPartialHomeomorph.extend_source] using h.mem_domChart_source
  obtain ⟨e, he, himage, hpoint⟩ := embedding_local_set_model hf.isEmbedding e₀
    (h.domChart.extend I) h.domChart.isOpen_extend_source hmap hcoord
    (h.domChart.open_target.preimage I.continuous_symm)
    h.domChart.extend_target hx
  exact ⟨h.domChart, e, h.domChart_mem_maximalAtlas, h.mem_domChart_source,
    he, himage, hpoint⟩

end PoincareConjecture.Topology.FiberSaturation
