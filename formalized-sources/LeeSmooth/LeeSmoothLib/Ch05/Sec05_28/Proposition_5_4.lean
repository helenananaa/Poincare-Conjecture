import Mathlib
import LeeSmoothLib.Ch01.Sec01.Example_1_3
universe uE uF uG uM uN

open Set Function
open scoped Manifold ContDiff Topology

namespace TopologicalSpace.Opens

variable {M : Type uM} [TopologicalSpace M] {N : Type uN}

/-- The chapter-5 `Opens`-typed graph parametrization is the open-subset view of the canonical
set-typed parametrization from Example 1.3. -/
abbrev graphMap (U : TopologicalSpace.Opens M) (f : M → N) : U → M × N :=
  _root_.graphMap (U : Set M) f

/-- The image of the `Opens`-typed graph parametrization is the graph over the underlying open
set. -/
theorem range_graphMap_eq_graphOn (U : TopologicalSpace.Opens M) (f : M → N) :
    Set.range (graphMap U f) = (U : Set M).graphOn f :=
  _root_.range_graphMap_eq_graphOn (U : Set M) f

end TopologicalSpace.Opens

variable {r : ℕ∞ω}

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type uG} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace E M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable [IsManifold (modelWithCornersSelf ℝ E) r M]
variable [IsManifold J r N]

open Manifold

omit [IsManifold (modelWithCornersSelf ℝ E) r M] [IsManifold J r N] in
/-- Smoothness of the graph parametrization `x ↦ (x, f x)` on an open subset. -/
theorem graphMap_contMDiff (U : TopologicalSpace.Opens M) (f : M → N)
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) J r f U) :
    ContMDiff (modelWithCornersSelf ℝ E) ((modelWithCornersSelf ℝ E).prod J)
      r (TopologicalSpace.Opens.graphMap U f) := by
  have hval : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
      r (Subtype.val : U → M) :=
    contMDiff_subtype_val
  have hfU : ContMDiff (modelWithCornersSelf ℝ E) J r
      (fun x : U ↦ f x) := by
    intro x
    rw [contMDiffAt_subtype_iff]
    exact hf.contMDiffAt (U.isOpen.mem_nhds x.2)
  exact hval.prodMk hfU

/-- Fibre-coordinate shear of the product model on an open set `Ω ⊆ E`, valid when
`range J = univ`. -/
noncomputable def graphShearPartialOn (g : E → F) (Ω : Set E) (hΩ : IsOpen Ω)
    (hg : ContinuousOn g Ω) (hrange : range (J : G → F) = univ) :
    OpenPartialHomeomorph (ModelProd E G) (ModelProd E G) where
  toFun := fun p ↦ (p.1, J.symm (J p.2 - g p.1))
  invFun := fun p ↦ (p.1, J.symm (J p.2 + g p.1))
  source := (Ω ×ˢ univ : Set (ModelProd E G))
  target := (Ω ×ˢ univ : Set (ModelProd E G))
  map_source' := fun p hp ↦ ⟨hp.1, mem_univ _⟩
  map_target' := fun p hp ↦ ⟨hp.1, mem_univ _⟩
  left_inv' := by
    intro p hp
    ext
    · rfl
    · change J.symm (J (J.symm (J p.2 - g p.1)) + g p.1) = p.2
      rw [J.right_inv (by rw [hrange]; exact mem_univ _), sub_add_cancel, J.left_inv]
  right_inv' := by
    intro p hp
    ext
    · rfl
    · change J.symm (J (J.symm (J p.2 + g p.1)) - g p.1) = p.2
      rw [J.right_inv (by rw [hrange]; exact mem_univ _), add_sub_cancel_right, J.left_inv]
  open_source := hΩ.prod isOpen_univ
  open_target := hΩ.prod isOpen_univ
  continuousOn_toFun :=
    continuousOn_fst.prodMk <| J.continuous_symm.comp_continuousOn <|
      (J.continuous.comp continuous_snd).continuousOn.sub
        (hg.comp continuousOn_fst fun p hp ↦ hp.1)
  continuousOn_invFun :=
    continuousOn_fst.prodMk <| J.continuous_symm.comp_continuousOn <|
      (J.continuous.comp continuous_snd).continuousOn.add
        (hg.comp continuousOn_fst fun p hp ↦ hp.1)

/-- In extended product coordinates the fibre shear is `(u, v) ↦ (u, v - g u)`. -/
theorem graphShearPartialOn_written_sub (g : E → F) (Ω : Set E) (hΩ : IsOpen Ω)
    (hg : ContinuousOn g Ω) (hrange : range (J : G → F) = univ) (q : E × F) :
    ((modelWithCornersSelf ℝ E).prod J)
        (graphShearPartialOn (J := J) g Ω hΩ hg hrange
          (((modelWithCornersSelf ℝ E).prod J).symm q)) =
      (q.1, J (J.symm (J (J.symm q.2) - g q.1))) := by
  simp [graphShearPartialOn, modelWithCorners_prod_coe, modelWithCorners_prod_coe_symm,
    modelWithCornersSelf_coe]

/-- In extended product coordinates the inverse fibre shear is `(u, v) ↦ (u, v + g u)`. -/
theorem graphShearPartialOn_written_add (g : E → F) (Ω : Set E) (hΩ : IsOpen Ω)
    (hg : ContinuousOn g Ω) (hrange : range (J : G → F) = univ) (q : E × F) :
    ((modelWithCornersSelf ℝ E).prod J)
        ((graphShearPartialOn (J := J) g Ω hΩ hg hrange).symm
          (((modelWithCornersSelf ℝ E).prod J).symm q)) =
      (q.1, J (J.symm (J (J.symm q.2) + g q.1))) := by
  simp [graphShearPartialOn, modelWithCorners_prod_coe, modelWithCorners_prod_coe_symm,
    modelWithCornersSelf_coe]

/-- The fibre shear lies in the `C^r` structure groupoid of the product model. -/
theorem graphShearPartialOn_mem_contDiffGroupoid [J.Boundaryless]
    (g : E → F) (Ω : Set E) (hΩ : IsOpen Ω) (hg : ContDiffOn ℝ r g Ω)
    (hrange : range (J : G → F) = univ) :
    graphShearPartialOn (J := J) g Ω hΩ hg.continuousOn hrange ∈
      contDiffGroupoid r ((modelWithCornersSelf ℝ E).prod J) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  set τ := graphShearPartialOn (J := J) g Ω hΩ hg.continuousOn hrange
  set Iprod := (modelWithCornersSelf ℝ E).prod J
  have hrangeI : range Iprod = (univ : Set (E × F)) := Iprod.range_eq_univ
  have hset : Iprod.symm ⁻¹' τ.source ∩ range Iprod = (Ω ×ˢ (univ : Set F)) := by
    rw [hrangeI, inter_univ]
    ext q
    change (q.1, J.symm q.2) ∈ (Ω ×ˢ (univ : Set G)) ↔ q ∈ Ω ×ˢ (univ : Set F)
    simp [mem_prod]
  constructor
  · change ContDiffOn ℝ r (Iprod ∘ τ ∘ Iprod.symm) (Iprod.symm ⁻¹' τ.source ∩ range Iprod)
    rw [hset]
    refine (contDiffOn_fst.prodMk
        (contDiffOn_snd.sub (hg.comp contDiffOn_fst fun q hq ↦ hq.1))).congr ?_
    intro q hq
    have hq2 : q.2 ∈ range (J : G → F) := by rw [hrange]; exact mem_univ _
    have hsub : q.2 - g q.1 ∈ range (J : G → F) := by rw [hrange]; exact mem_univ _
    have hwr := graphShearPartialOn_written_sub (J := J) g Ω hΩ hg.continuousOn hrange q
    rw [J.right_inv hq2, J.right_inv hsub] at hwr
    simpa [τ, Iprod, Function.comp] using hwr
  · change ContDiffOn ℝ r (Iprod ∘ τ.symm ∘ Iprod.symm) (Iprod.symm ⁻¹' τ.target ∩ range Iprod)
    have hset' : Iprod.symm ⁻¹' τ.target ∩ range Iprod = (Ω ×ˢ (univ : Set F)) := by
      simpa [τ, graphShearPartialOn] using hset
    rw [hset']
    refine (contDiffOn_fst.prodMk
        (contDiffOn_snd.add (hg.comp contDiffOn_fst fun q hq ↦ hq.1))).congr ?_
    intro q hq
    have hq2 : q.2 ∈ range (J : G → F) := by rw [hrange]; exact mem_univ _
    have hadd : q.2 + g q.1 ∈ range (J : G → F) := by rw [hrange]; exact mem_univ _
    have hwr := graphShearPartialOn_written_add (J := J) g Ω hΩ hg.continuousOn hrange q
    rw [J.right_inv hq2, J.right_inv hadd] at hwr
    simpa [τ, Iprod, Function.comp] using hwr

/-- Proposition 5.4: for a smooth map on an open subset of a smooth manifold without boundary, the
canonical graph parametrization into the product manifold is a smooth embedding, so its image is an
embedded submanifold of the ambient product. -/
-- Proof sketch: the map `x ↦ (x, f x)` is smooth by combining the inclusion of the open subset
-- with `f`; the first projection is a left inverse, so the differential is injective and the map
-- is an immersion. The first projection also gives a continuous inverse from the image back to the
-- domain, so the map is a topological embedding.
theorem graphMap_isSmoothEmbedding [J.Boundaryless] (U : TopologicalSpace.Opens M) (f : M → N)
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) J r f U) :
    Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod J) r (TopologicalSpace.Opens.graphMap U f) := by
  refine ⟨?immersion, graphMap_isEmbedding (U : Set M) f hf.continuousOn⟩
  have himm : IsImmersion (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod J) r (TopologicalSpace.Opens.graphMap U f) := by
    apply IsImmersionOfComplement.isImmersion (F := F)
    intro x
    have _ : Nonempty U := ⟨x⟩
    let eU : OpenPartialHomeomorph U E := chartAt E x
    let eM : OpenPartialHomeomorph M E := chartAt E (x : M)
    let eN : OpenPartialHomeomorph N G := chartAt G (f (x : M))
    let eProd : OpenPartialHomeomorph (M × N) (ModelProd E G) := eM.prod eN
    let g : E → F := writtenInExtChartAt (modelWithCornersSelf ℝ E) J (x : M) f
    have hxM : (x : M) ∈ eM.source := mem_chart_source E (x : M)
    have hfN : f (x : M) ∈ eN.source := mem_chart_source G (f (x : M))
    let U' : Set M := ((U : Set M) ∩ f ⁻¹' eN.source) ∩ eM.source
    have hU'open : IsOpen U' :=
      (hf.continuousOn.isOpen_inter_preimage U.isOpen eN.open_source).inter eM.open_source
    have hU'sub : U' ⊆ eM.source := inter_subset_right
    have hU'maps : MapsTo f U' eN.source := fun z hz ↦ hz.1.2
    have hfU' : ContMDiffOn (modelWithCornersSelf ℝ E) J r f U' :=
      hf.mono fun z hz ↦ hz.1.1
    have hgOn : ContDiffOn ℝ r g (eM.extend (modelWithCornersSelf ℝ E) '' U') := by
      have h := (contMDiffOn_iff_of_subset_source (I := modelWithCornersSelf ℝ E) (I' := J)
        (n := r) (x := (x : M)) (y := f (x : M)) hU'sub hU'maps).1 hfU'
      simpa [g, writtenInExtChartAt, extChartAt] using h.2
    let Ω : Set E := eM.extend (modelWithCornersSelf ℝ E) '' U'
    have hΩopen : IsOpen Ω := by
      simpa [Ω, OpenPartialHomeomorph.extend] using
        eM.isOpen_image_of_subset_source hU'open hU'sub
    have hxΩ : eM (x : M) ∈ Ω := by
      refine ⟨(x : M), ⟨⟨x.2, hfN⟩, hxM⟩, ?_⟩
      simp [OpenPartialHomeomorph.extend]
    have hgC : ContinuousOn g Ω := hgOn.continuousOn
    have hγ : ContinuousAt (TopologicalSpace.Opens.graphMap U f) x :=
      (graphMap_contMDiff U f hf x).continuousAt
    have hrange : range (J : G → F) = univ := J.range_eq_univ
    let τ := graphShearPartialOn (J := J) g Ω hΩopen hgC hrange
    let eCod : OpenPartialHomeomorph (M × N) (ModelProd E G) := eProd.trans τ
    refine IsImmersionAtOfComplement.mk_of_continuousAt (n := r) hγ
      (ContinuousLinearEquiv.refl ℝ (E × F)) eU eCod ?hx ?hfx ?hdom ?hcod ?hwritten
    · exact mem_chart_source E x
    · exact ⟨⟨hxM, hfN⟩, ⟨hxΩ, mem_univ _⟩⟩
    · exact IsManifold.chart_mem_maximalAtlas
        (I := modelWithCornersSelf ℝ E) (n := r) x
    · have heProd : eProd ∈ IsManifold.maximalAtlas
          ((modelWithCornersSelf ℝ E).prod J) r (M × N) :=
        IsManifold.mem_maximalAtlas_prod
          (IsManifold.chart_mem_maximalAtlas
            (I := modelWithCornersSelf ℝ E) (n := r) (x : M))
          (IsManifold.chart_mem_maximalAtlas
            (I := J) (n := r) (f (x : M)))
      have hτg : τ ∈ contDiffGroupoid r ((modelWithCornersSelf ℝ E).prod J) :=
        graphShearPartialOn_mem_contDiffGroupoid (J := J) g Ω hΩopen hgOn hrange
      have hτ : ContMDiffOn ((modelWithCornersSelf ℝ E).prod J)
          ((modelWithCornersSelf ℝ E).prod J) r τ τ.source :=
        contMDiffOn_of_mem_contDiffGroupoid hτg
      have hτsymm : ContMDiffOn ((modelWithCornersSelf ℝ E).prod J)
          ((modelWithCornersSelf ℝ E).prod J) r τ.symm τ.target :=
        contMDiffOn_of_mem_contDiffGroupoid
          (StructureGroupoid.symm (contDiffGroupoid r ((modelWithCornersSelf ℝ E).prod J)) hτg)
      refine eCod.mem_maximalAtlas_of_contMDiffOn
        (I := (modelWithCornersSelf ℝ E).prod J) (n := r) ?fwd ?inv
      · have hProd := contMDiffOn_of_mem_maximalAtlas
            (I := (modelWithCornersSelf ℝ E).prod J) (n := r) heProd
        rw [OpenPartialHomeomorph.trans_source]
        exact hτ.comp' hProd
      · have hProd := contMDiffOn_symm_of_mem_maximalAtlas
            (I := (modelWithCornersSelf ℝ E).prod J) (n := r) heProd
        rw [OpenPartialHomeomorph.trans_target]
        exact hProd.comp' hτsymm
    · intro u hu
      have hchart : eU = eM.subtypeRestr ⟨x⟩ := TopologicalSpace.Opens.chartAt_eq (s := U)
      set x' : U := (eU.extend (modelWithCornersSelf ℝ E)).symm u
      have hx'M : (x' : M) ∈ eM.source := by
        have hxU : (eU.extend (modelWithCornersSelf ℝ E)).symm u ∈
            (eU.extend (modelWithCornersSelf ℝ E)).source :=
          (eU.extend (modelWithCornersSelf ℝ E)).map_target hu
        simpa [hchart, OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.extend,
          modelWithCornersSelf_coe, x'] using hxU
      have huM : eM (x' : M) = u := by
        have : eU x' = u := by
          have := (eU.extend (modelWithCornersSelf ℝ E)).right_inv hu
          simpa [OpenPartialHomeomorph.extend, x'] using this
        simpa [hchart, OpenPartialHomeomorph.subtypeRestr_coe] using this
      have hgraph :
          TopologicalSpace.Opens.graphMap U f
              ((eU.extend (modelWithCornersSelf ℝ E)).symm u) =
            ((x' : M), f (x' : M)) := by
        simp [TopologicalSpace.Opens.graphMap, graphMap, x', OpenPartialHomeomorph.extend]
      have hcod :
          eCod ((x' : M), f (x' : M)) =
            (eM (x' : M), J.symm (J (eN (f (x' : M))) - g (eM (x' : M)))) := by
        change τ (eProd ((x' : M), f (x' : M))) = _
        change τ (eM (x' : M), eN (f (x' : M))) = _
        rfl
      have hgEq : g (eM (x' : M)) = J (eN (f (x' : M))) := by
        simp [g, writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend]
        rw [eM.left_inv hx'M]
      have h0 : J (J.symm (J (eN (f (x' : M))) - g (eM (x' : M)))) = 0 := by
        rw [J.right_inv (by rw [hrange]; exact mem_univ _), hgEq, sub_self]
      simp only [Function.comp_apply]
      rw [hgraph]
      simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply]
      rw [hcod, modelWithCorners_prod_coe]
      refine Prod.ext ?_ ?_
      · simp [modelWithCornersSelf_coe, huM]
      · simpa [ContinuousLinearEquiv.refl_apply] using h0
  exact himm
