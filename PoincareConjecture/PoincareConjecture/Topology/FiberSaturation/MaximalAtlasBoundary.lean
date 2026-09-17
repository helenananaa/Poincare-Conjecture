import PoincareConjecture.Topology.FiberSaturation.CodimensionZeroCharts

/-!
The chart-invariance proof below generalizes Mathlib's
`mem_interior_range_of_mem_interior_range_of_mem_atlas` to maximal-atlas charts.
Adapted from Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean
at 520045ab14e26149ee970e2e617ca04b09bde5d6 (Apache-2.0).
-/
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Function ModelWithCorners Filter _root_.Topology
open scoped Manifold ContDiff Topology

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞} [IsManifold I n M]
  {e e' : OpenPartialHomeomorph M H} {x : M}

lemma interior_transfer_maximalAtlas (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M) (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  /- Since transition maps are diffeomorphisms, it suffices to show that if `e'` were to send `x`
  to the boundary of `range I`, the differential of the transition map `φ` from `e` to `e'` at `x`
  could not be surjective. -/
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := contDiffOn_extendCoordChange
    he he'
  suffices h : Function.Surjective (fderivWithin 𝕜 φ φ.source (e.extend I x)) →
      e'.extend I x ∈ interior (range I) by
    refine e'.mem_interior_extend_target (by simp [hex']) <| h ?_
    exact (isInvertible_fderivWithin_extendCoordChange hn he
      he' <| by simp [hex, hex']).surjective
  intro hφx'
  /- Reduce the situation to the real case, then apply
  `DifferentiableAt.mem_interior_convex_of_surjective_fderiv`. -/
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [I.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hφx : φ.source ∈ 𝓝 (e.extend I x) := by
    simp_rw [φ, extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      Filter.inter_mem_iff, mem_interior_iff_mem_nhds.1 hx, true_and, e'.extend_source]
    exact e.extend_preimage_mem_nhds hex <| e'.open_source.mem_nhds hex'
  rw [← ContinuousLinearMap.coe_restrictScalars' (R := ℝ),
    (hφ.differentiableOn hn _ (by simp [φ, hex, hex'])).restrictScalars_fderivWithin (𝕜 := ℝ)
      (uniqueDiffWithinAt_of_mem_nhds hφx), fderivWithin_of_mem_nhds <| hφx] at hφx'
  rw [show e'.extend I x = φ (e.extend I x) by simp [φ, hex]]
  replace hφ := ((hφ.restrict_scalars ℝ).differentiableOn hn).differentiableAt hφx
  exact hφ.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
    I.nonempty_interior (φ.mapsTo.mono_right <| by simp [φ, inter_assoc]) hφx'

/-- Intrinsic interior can be read in any compatible maximal-atlas chart. -/
theorem intrinsicInterior_iff_maximalChart (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ e.extend I x ∈ interior (range I) := by
  rw [I.isInteriorPoint_iff]
  constructor
  · intro hp
    have h := interior_transfer_maximalAtlas hn (IsManifold.chart_mem_maximalAtlas x)
      he (mem_chart_source H x) hx hp
    exact e.interior_extend_target_subset_interior_range h
  · intro hp
    exact interior_transfer_maximalAtlas hn he (IsManifold.chart_mem_maximalAtlas x)
      hx (mem_chart_source H x) (e.mem_interior_extend_target (e.map_source hx) hp)

/-- The boundary predicate is likewise invariant for maximal-atlas charts. -/
theorem intrinsicBoundary_iff_maximalChart (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ e.extend I x ∈ frontier (range I) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint,
    intrinsicInterior_iff_maximalChart hn he hx, frontier, I.isClosed_range.closure_eq]
  have hmem : e.extend I x ∈ range I := ⟨e x, rfl⟩
  simp only [Set.mem_sdiff, hmem, true_and]

end PoincareConjecture.Topology.FiberSaturation
