import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_2
import LeeSmoothLib.Ch01.Sec01_06.Theorem_1_46
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
-- Declarations for this item will be appended below by the statement pipeline.

open Set Function
open scoped ContDiff Manifold Topology

noncomputable section

universe uE uH uM

-- Semantic recall note: no `lean_leansearch` tool was available in this environment; local
-- repository and mathlib inspection verified `Set.IsRegularDomain` together with
-- `ModelWithCorners.interior` and `ModelWithCorners.boundary` as the canonical owners here.

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]

local notation "dimM" => Module.finrank ℝ E
local notation "J" => leeBoundaryModelWithCorners dimM

/-- An equal-dimensional embedding, written in charts, becomes an exact local set model after
shrinking the ambient chart. Global embedding excludes other source points from the neighbourhood.
-/
private theorem embedding_local_set_model {A B V : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace V] {f : A → B}
    (hf : Topology.IsEmbedding f) (e₀ : OpenPartialHomeomorph B V)
    (g : PartialEquiv A V) (hg : IsOpen g.source)
    (hmap : MapsTo f g.source e₀.source)
    (hcoord : EqOn (e₀ ∘ f) g g.source)
    {O R : Set V} (hO : IsOpen O) (htarget : g.target = O ∩ R)
    {x : A} (hx : x ∈ g.source) :
    ∃ e : OpenPartialHomeomorph B V,
      f x ∈ e.source ∧ e.IsImage (range f) R ∧ e (f x) = g x := by
  obtain ⟨W, hW, hpre⟩ := hf.isInducing.isOpen_iff.mp hg
  let S : Set B := W ∩ (e₀.source ∩ e₀ ⁻¹' O)
  have hS : IsOpen S := hW.inter (e₀.isOpen_inter_preimage hO)
  let e := e₀.restr S
  have hfx : f x ∈ e.source := by
    rw [e₀.restr_source' S hS]
    refine ⟨hmap hx, ?_, hmap hx, ?_⟩
    · change x ∈ f ⁻¹' W
      rwa [hpre]
    · change e₀ (f x) ∈ O
      rw [show e₀ (f x) = g x from hcoord hx]
      exact (htarget ▸ g.map_source hx).1
  refine ⟨e, hfx, ?_, hcoord hx⟩
  intro y hy
  have hy' : y ∈ e₀.source ∩ S := by rwa [e₀.restr_source' S hS] at hy
  change e₀ y ∈ R ↔ y ∈ range f
  constructor
  · intro hyr
    have hyt : e₀ y ∈ g.target := htarget ▸ ⟨hy'.2.2.2, hyr⟩
    refine ⟨g.symm (e₀ y), ?_⟩
    apply e₀.injOn (hmap (g.map_target hyt)) hy'.1
    exact (hcoord (g.map_target hyt)).trans (g.right_inv hyt)
  · rintro ⟨z, rfl⟩
    have hz : z ∈ g.source := by
      rw [← hpre]
      exact hy'.2.1
    rw [show e₀ (f z) = g z from hcoord hz]
    exact (htarget ▸ g.map_source hz).2

/-- At an interior point of a boundaryless ambient manifold, the extended chart shrinks to an
honest `E`-valued open partial homeomorphism. -/
private noncomputable def extendInteriorChart (I : ModelWithCorners ℝ E H)
    (e : OpenPartialHomeomorph M H) : OpenPartialHomeomorph M E where
  toPartialEquiv :=
    { toFun := e.extend I
      invFun := (e.extend I).symm
      source := (e.extend I) ⁻¹' interior (e.extend I).target ∩ (e.extend I).source
      target := interior (e.extend I).target
      map_source' := fun _ hy ↦ hy.1
      map_target' := fun y hy ↦ by
        have hyTarget : y ∈ (e.extend I).target := interior_subset hy
        have hySource : (e.extend I).symm y ∈ (e.extend I).source :=
          (e.extend I).map_target hyTarget
        have hyEq : e.extend I ((e.extend I).symm y) = y :=
          PartialEquiv.right_inv (e.extend I) hyTarget
        refine ⟨?_, hySource⟩
        show e.extend I ((e.extend I).symm y) ∈ interior (e.extend I).target
        rw [hyEq]
        exact hy
      left_inv' := fun _ hy ↦ PartialEquiv.left_inv (e.extend I) hy.2
      right_inv' := fun _ hy ↦ PartialEquiv.right_inv (e.extend I) (interior_subset hy) }
  open_source := by
    rw [inter_comm, e.extend_source]
    exact e.isOpen_extend_preimage (I := I) isOpen_interior
  open_target := isOpen_interior
  continuousOn_toFun := by
    intro y hy
    exact ((e.continuousOn_extend (I := I)) y hy.2).mono fun _ hz ↦ hz.2
  continuousOn_invFun := by
    intro y hy
    exact ((e.continuousOn_extend_symm (I := I)) y (interior_subset hy)).mono
      fun _ hz ↦ interior_subset hz

/-- Interior points may be read in any maximal-atlas chart as membership in `interior (range I)`. -/
private theorem isInteriorPoint_iff_mem_interior_range
    {H' : Type*} [TopologicalSpace H'] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    {e : OpenPartialHomeomorph N H'} {x : N}
    (he : e ∈ IsManifold.maximalAtlas I' ∞ N) (hx : x ∈ e.source) :
    I'.IsInteriorPoint x ↔ e.extend I' x ∈ interior (range I') := by
  rw [I'.isInteriorPoint_iff_of_mem_maximalAtlas (n := ∞) (by simp) he hx]
  constructor
  · exact fun h ↦ e.interior_extend_target_subset_interior_range h
  · intro h
    exact e.mem_interior_extend_target (e.map_source hx) h

/-- Boundary points may be read in any maximal-atlas chart as membership in `frontier (range I)`. -/
private theorem isBoundaryPoint_iff_mem_frontier_range
    {H' : Type*} [TopologicalSpace H'] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    {e : OpenPartialHomeomorph N H'} {x : N}
    (he : e ∈ IsManifold.maximalAtlas I' ∞ N) (hx : x ∈ e.source) :
    I'.IsBoundaryPoint x ↔ e.extend I' x ∈ frontier (range I') := by
  have hmem : e.extend I' x ∈ range I' := ⟨e x, rfl⟩
  rw [I'.isBoundaryPoint_iff_not_isInteriorPoint,
    isInteriorPoint_iff_mem_interior_range he hx, frontier, I'.isClosed_range.closure_eq,
    mem_sdiff, and_iff_right hmem]

/-- Equal-dimensional smooth embeddings into a boundaryless ambient manifold admit exact ambient
set charts compatible with a source maximal-atlas chart. -/
private theorem exists_codimensionZero_ambient_chart {D : Set M}
    [SmoothManifoldWithBoundary dimM D] {f : D → M}
    (hf : Manifold.IsSmoothEmbedding J I ∞ f)
    (hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin dimM)) = Module.finrank ℝ E) (x : D) :
    ∃ a : OpenPartialHomeomorph D (ℍ^{dimM}),
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
        a ∈ IsManifold.maximalAtlas J ∞ D ∧ x ∈ a.source ∧
          f x ∈ e.source ∧ e.IsImage (range f) (range J) ∧
            e (f x) = a.extend J x := by
  obtain ⟨C, hCgroup, hCspace, hC⟩ := hf.isImmersion
  letI := hCgroup
  letI := hCspace
  let h := hC x
  let k : C →ₗ[ℝ] E :=
    (h.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin dimM)) C)).toLinearMap
  have hkinj : Injective k := by
    intro u v huv
    exact congrArg Prod.snd (h.equiv.injective huv)
  letI : FiniteDimensional ℝ C := FiniteDimensional.of_injective k hkinj
  have hzero : Module.finrank ℝ C = 0 := by
    have heq := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, hdim] at heq
    omega
  letI : Subsingleton C := Module.finrank_zero_iff.mp hzero
  letI : Unique C := ⟨⟨0⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let l : E ≃L[ℝ] EuclideanSpace ℝ (Fin dimM) :=
    h.equiv.symm.trans
      (ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin dimM)) C)
  let c : OpenPartialHomeomorph M E := extendInteriorChart I h.codChart
  have hfx_c : f x ∈ c.source := by
    refine ⟨?_, ?_⟩
    · change h.codChart.extend I (f x) ∈ interior (h.codChart.extend I).target
      exact (I.isInteriorPoint_iff_of_mem_maximalAtlas (n := ∞) (by simp)
          h.codChart_mem_maximalAtlas h.mem_codChart_source).1
        (show I.IsInteriorPoint (f x) from BoundarylessManifold.isInteriorPoint)
    · simpa [OpenPartialHomeomorph.extend_source] using h.mem_codChart_source
  let e₀ := c.transHomeomorph l.toHomeomorph
  have hfx_e₀ : f x ∈ e₀.source := by
    simpa [e₀, OpenPartialHomeomorph.transHomeomorph] using hfx_c
  let s : Set D := f ⁻¹' e₀.source
  have hs : IsOpen s := e₀.open_source.preimage hf.isEmbedding.continuous
  let a := h.domChart.restr s
  have hx_a : x ∈ a.source := by
    rw [h.domChart.restr_source' s hs]
    exact ⟨h.mem_domChart_source, hfx_e₀⟩
  have ha : a ∈ IsManifold.maximalAtlas J ∞ D :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ J) h.domChart_mem_maximalAtlas hs
  have hmap : MapsTo f (a.extend J).source e₀.source := by
    intro y hy
    rw [a.extend_source] at hy
    have : y ∈ a.source := hy
    rw [h.domChart.restr_source' s hs] at this
    exact this.2
  have hcoord : EqOn (e₀ ∘ f) (a.extend J) (a.extend J).source := by
    intro y hy
    have hy' : y ∈ h.domChart.source := by
      rw [a.extend_source] at hy
      exact (h.domChart.restr_source' s hs ▸ hy).1
    have hnormal := h.writtenInCharts ((h.domChart.extend J).map_source
      (by simpa [OpenPartialHomeomorph.extend_source] using hy'))
    simp only [comp_apply, (h.domChart.extend J).left_inv
      (by simpa [OpenPartialHomeomorph.extend_source] using hy')] at hnormal
    have hy_e₀ : f y ∈ e₀.source := hmap (by simpa [a.extend_source] using hy)
    change l (c (f y)) = a.extend J y
    have hc_eq : c (f y) = h.codChart.extend I (f y) := rfl
    rw [hc_eq, hnormal]
    have ha_eq : a.extend J y = h.domChart.extend J y := by
      simp [a]
    rw [ha_eq]
    simp [l]
  obtain ⟨e, he, himage, hpoint⟩ :=
    embedding_local_set_model hf.isEmbedding e₀ (a.extend J) a.isOpen_extend_source
      hmap hcoord
      (a.open_target.preimage (leeBoundaryModelWithCorners dimM).continuous_symm)
      a.extend_target
      (by simpa [a.extend_source] using hx_a)
  exact ⟨a, e, ha, hx_a, he, himage, hpoint⟩

/-- Proposition 5.46 (1): if `D ⊆ M` is a regular domain in a smooth manifold without boundary,
then the ambient topological interior of `D` is exactly the image of the manifold interior of `D`
under the subtype inclusion. -/
theorem regular_domain_manifoldInterior_image_eq_interior
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D] :
    Subtype.val '' (leeBoundaryModelWithCorners dimM).interior D = interior D := by
  let f : D → M := Subtype.val
  have hf : Manifold.IsSmoothEmbedding J I ∞ f :=
    (inferInstance : Set.IsRegularDomain I D).isSmoothEmbedding_subtype_val
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin dimM)) = Module.finrank ℝ E := by
    simp
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, e, ha, hxsrc, hfx, himage, hcoord⟩ :=
      exists_codimensionZero_ambient_chart hf hdim x
    have : f x ∈ interior (range f) := by
      rw [← (himage.interior hfx), hcoord]
      exact (isInteriorPoint_iff_mem_interior_range ha hxsrc).mp hx
    simpa [f, Subtype.range_val] using this
  · intro hy
    let x : D := ⟨y, interior_subset hy⟩
    obtain ⟨a, e, ha, hxsrc, hfx, himage, hcoord⟩ :=
      exists_codimensionZero_ambient_chart hf hdim x
    refine ⟨x, ?_, rfl⟩
    exact (isInteriorPoint_iff_mem_interior_range ha hxsrc).mpr <| by
      rw [← hcoord, himage.interior hfx]
      simpa [f, Subtype.range_val] using hy

/-- Proposition 5.46 (2): if `D ⊆ M` is a regular domain in a smooth manifold without boundary,
then the ambient topological boundary of `D` is exactly the image of the manifold boundary of `D`
under the subtype inclusion. -/
theorem regular_domain_manifoldBoundary_image_eq_frontier
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D] :
    Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary D = frontier D := by
  let f : D → M := Subtype.val
  have hf : Manifold.IsSmoothEmbedding J I ∞ f :=
    (inferInstance : Set.IsRegularDomain I D).isSmoothEmbedding_subtype_val
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin dimM)) = Module.finrank ℝ E := by
    simp
  have hD : IsClosed D := by
    simpa [Subtype.range_val] using
      (inferInstance : Set.IsRegularDomain I D).isProperlyEmbedded.isClosed_range
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, e, ha, hxsrc, hfx, himage, hcoord⟩ :=
      exists_codimensionZero_ambient_chart hf hdim x
    have : f x ∈ frontier (range f) := by
      rw [← (himage.frontier hfx), hcoord]
      exact (isBoundaryPoint_iff_mem_frontier_range ha hxsrc).mp hx
    simpa [f, Subtype.range_val] using this
  · intro hy
    have hyD : y ∈ D := hD.closure_eq ▸ hy.1
    let x : D := ⟨y, hyD⟩
    obtain ⟨a, e, ha, hxsrc, hfx, himage, hcoord⟩ :=
      exists_codimensionZero_ambient_chart hf hdim x
    refine ⟨x, ?_, rfl⟩
    exact (isBoundaryPoint_iff_mem_frontier_range ha hxsrc).mpr <| by
      rw [← hcoord, himage.frontier hfx]
      simpa [f, Subtype.range_val] using hy
