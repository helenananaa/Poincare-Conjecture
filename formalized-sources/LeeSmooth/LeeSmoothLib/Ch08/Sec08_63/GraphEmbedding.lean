import Mathlib
import LeeSmoothLib.Ch01.Sec01.Example_1_3

open Set Function Manifold
open scoped Manifold ContDiff Topology

universe uE uF uH uG uM uN

noncomputable section

variable {r : ℕ∞ω}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type uG} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable [IsManifold I r M] [IsManifold J r N]

/-- The local product-coordinate shear `(u,v) ↦ (u,v-g(u))`, expressed on arbitrary
boundaryless real models.  This is the chart change that straightens a graph. -/
def graphShearPartialOnGeneral [I.Boundaryless] [J.Boundaryless]
    (g : E → F) (Ω : Set E) (hΩ : IsOpen Ω) (hg : ContinuousOn g Ω) :
    OpenPartialHomeomorph (ModelProd H G) (ModelProd H G) where
  toFun := fun p ↦ (p.1, J.symm (J p.2 - g (I p.1)))
  invFun := fun p ↦ (p.1, J.symm (J p.2 + g (I p.1)))
  source := (I ⁻¹' Ω) ×ˢ univ
  target := (I ⁻¹' Ω) ×ˢ univ
  map_source' := fun p hp ↦ ⟨hp.1, mem_univ _⟩
  map_target' := fun p hp ↦ ⟨hp.1, mem_univ _⟩
  left_inv' := by
    intro p hp
    ext
    · rfl
    · change J.symm (J (J.symm (J p.2 - g (I p.1))) + g (I p.1)) = p.2
      rw [J.right_inv (by rw [J.range_eq_univ]; exact mem_univ _), sub_add_cancel, J.left_inv]
  right_inv' := by
    intro p hp
    ext
    · rfl
    · change J.symm (J (J.symm (J p.2 + g (I p.1))) - g (I p.1)) = p.2
      rw [J.right_inv (by rw [J.range_eq_univ]; exact mem_univ _), add_sub_cancel_right,
        J.left_inv]
  open_source := (hΩ.preimage I.continuous).prod isOpen_univ
  open_target := (hΩ.preimage I.continuous).prod isOpen_univ
  continuousOn_toFun :=
    continuousOn_fst.prodMk <| J.continuous_symm.comp_continuousOn <|
      (J.continuous.comp continuous_snd).continuousOn.sub
        (hg.comp (I.continuous.comp continuous_fst).continuousOn fun p hp ↦ hp.1)
  continuousOn_invFun :=
    continuousOn_fst.prodMk <| J.continuous_symm.comp_continuousOn <|
      (J.continuous.comp continuous_snd).continuousOn.add
        (hg.comp (I.continuous.comp continuous_fst).continuousOn fun p hp ↦ hp.1)

/-- In extended product coordinates, the general-model graph shear is exactly subtraction in the
second factor. -/
lemma graphShearPartialOnGeneral_written_sub [I.Boundaryless] [J.Boundaryless]
    (g : E → F) (Ω : Set E) (hΩ : IsOpen Ω) (hg : ContinuousOn g Ω) (q : E × F) :
    (I.prod J)
        (graphShearPartialOnGeneral (I := I) (J := J) g Ω hΩ hg
          ((I.prod J).symm q)) =
      (q.1, q.2 - g q.1) := by
  have hq1 : q.1 ∈ range (I : H → E) := by rw [I.range_eq_univ]; exact mem_univ _
  have hq2 : q.2 ∈ range (J : G → F) := by rw [J.range_eq_univ]; exact mem_univ _
  have hsub : q.2 - g q.1 ∈ range (J : G → F) := by
    rw [J.range_eq_univ]
    exact mem_univ _
  simp [graphShearPartialOnGeneral, modelWithCorners_prod_coe,
    modelWithCorners_prod_coe_symm, I.right_inv hq1, J.right_inv hq2, J.right_inv hsub]

/-- The inverse general-model graph shear is exactly addition in extended product coordinates. -/
lemma graphShearPartialOnGeneral_written_add [I.Boundaryless] [J.Boundaryless]
    (g : E → F) (Ω : Set E) (hΩ : IsOpen Ω) (hg : ContinuousOn g Ω) (q : E × F) :
    (I.prod J)
        ((graphShearPartialOnGeneral (I := I) (J := J) g Ω hΩ hg).symm
          ((I.prod J).symm q)) =
      (q.1, q.2 + g q.1) := by
  have hq1 : q.1 ∈ range (I : H → E) := by rw [I.range_eq_univ]; exact mem_univ _
  have hq2 : q.2 ∈ range (J : G → F) := by rw [J.range_eq_univ]; exact mem_univ _
  have hadd : q.2 + g q.1 ∈ range (J : G → F) := by
    rw [J.range_eq_univ]
    exact mem_univ _
  simp [graphShearPartialOnGeneral, modelWithCorners_prod_coe,
    modelWithCorners_prod_coe_symm, I.right_inv hq1, J.right_inv hq2, J.right_inv hadd]

/-- The graph-straightening shear is a `C^r` change of charts for arbitrary boundaryless real
models. -/
lemma graphShearPartialOnGeneral_mem_contDiffGroupoid [I.Boundaryless] [J.Boundaryless]
    (g : E → F) (Ω : Set E) (hΩ : IsOpen Ω) (hg : ContDiffOn ℝ r g Ω) :
    graphShearPartialOnGeneral (I := I) (J := J) g Ω hΩ hg.continuousOn ∈
      contDiffGroupoid r (I.prod J) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  set τ := graphShearPartialOnGeneral (I := I) (J := J) g Ω hΩ hg.continuousOn
  set Iprod := I.prod J
  have hrangeI : range Iprod = (univ : Set (E × F)) := Iprod.range_eq_univ
  have hset : Iprod.symm ⁻¹' τ.source ∩ range Iprod = (Ω ×ˢ (univ : Set F)) := by
    rw [hrangeI, inter_univ]
    ext q
    have hq1 : q.1 ∈ range (I : H → E) := by rw [I.range_eq_univ]; exact mem_univ _
    simp only [Set.mem_preimage, τ, Iprod, graphShearPartialOnGeneral,
      modelWithCorners_prod_coe_symm, Set.mem_prod, mem_univ, and_true]
    constructor
    · rintro ⟨hq, -⟩
      change I (I.symm q.1) ∈ Ω at hq
      simpa [I.right_inv hq1] using hq
    · intro hq
      refine ⟨?_, mem_univ _⟩
      change I (I.symm q.1) ∈ Ω
      simpa [I.right_inv hq1] using hq
  constructor
  · change ContDiffOn ℝ r (Iprod ∘ τ ∘ Iprod.symm)
      (Iprod.symm ⁻¹' τ.source ∩ range Iprod)
    rw [hset]
    refine (contDiffOn_fst.prodMk
        (contDiffOn_snd.sub (hg.comp contDiffOn_fst fun q hq ↦ hq.1))).congr ?_
    intro q hq
    simpa [τ, Iprod, Function.comp] using
      graphShearPartialOnGeneral_written_sub (I := I) (J := J) g Ω hΩ hg.continuousOn q
  · change ContDiffOn ℝ r (Iprod ∘ τ.symm ∘ Iprod.symm)
      (Iprod.symm ⁻¹' τ.target ∩ range Iprod)
    have hset' : Iprod.symm ⁻¹' τ.target ∩ range Iprod = (Ω ×ˢ (univ : Set F)) := by
      simpa [τ, graphShearPartialOnGeneral] using hset
    rw [hset']
    refine (contDiffOn_fst.prodMk
        (contDiffOn_snd.add (hg.comp contDiffOn_fst fun q hq ↦ hq.1))).congr ?_
    intro q hq
    simpa [τ, Iprod, Function.comp] using
      graphShearPartialOnGeneral_written_add (I := I) (J := J) g Ω hΩ hg.continuousOn q

/-- A global smooth graph map is a smooth embedding for arbitrary boundaryless real models.  The
proof uses local product-chart shears and never replaces the given atlas by a self-model atlas. -/
theorem graphMap_isSmoothEmbedding_general [I.Boundaryless] [J.Boundaryless]
    (f : M → N) (hf : ContMDiff I J r f) :
    Manifold.IsSmoothEmbedding I (I.prod J) r (fun x : M ↦ (x, f x)) := by
  refine ⟨?_, ?_⟩
  · apply IsImmersionOfComplement.isImmersion (F := F)
    intro x
    let eM : OpenPartialHomeomorph M H := chartAt H x
    let eN : OpenPartialHomeomorph N G := chartAt G (f x)
    let eProd : OpenPartialHomeomorph (M × N) (ModelProd H G) := eM.prod eN
    let g : E → F := writtenInExtChartAt I J x f
    have hxM : x ∈ eM.source := mem_chart_source H x
    have hfN : f x ∈ eN.source := mem_chart_source G (f x)
    let U' : Set M := (f ⁻¹' eN.source) ∩ eM.source
    have hU'open : IsOpen U' :=
      (eN.open_source.preimage hf.continuous).inter eM.open_source
    have hU'sub : U' ⊆ eM.source := inter_subset_right
    have hU'maps : MapsTo f U' eN.source := fun z hz ↦ hz.1
    have hfU' : ContMDiffOn I J r f U' := hf.contMDiffOn
    have hgOn : ContDiffOn ℝ r g (eM.extend I '' U') := by
      have h := (contMDiffOn_iff_of_subset_source (I := I) (I' := J)
        (n := r) (x := x) (y := f x) hU'sub hU'maps).1 hfU'
      simpa [g, writtenInExtChartAt, extChartAt] using h.2
    let Ω : Set E := eM.extend I '' U'
    have hΩopen : IsOpen Ω := by
      have hopenH : IsOpen (eM '' U') :=
        eM.isOpen_image_of_subset_source hU'open hU'sub
      simpa [Ω, OpenPartialHomeomorph.extend, Set.image_image] using
        I.toHomeomorph.isOpenMap _ hopenH
    have hxΩ : I (eM x) ∈ Ω := by
      refine ⟨x, ⟨hfN, hxM⟩, ?_⟩
      simp [OpenPartialHomeomorph.extend]
    have hγ : ContinuousAt (fun z : M ↦ (z, f z)) x :=
      (contMDiffAt_id.prodMk hf.contMDiffAt).continuousAt
    let τ := graphShearPartialOnGeneral (I := I) (J := J) g Ω hΩopen hgOn.continuousOn
    let eCod : OpenPartialHomeomorph (M × N) (ModelProd H G) := eProd.trans τ
    refine IsImmersionAtOfComplement.mk_of_continuousAt (n := r) hγ
      (ContinuousLinearEquiv.refl ℝ (E × F)) eM eCod ?_ ?_ ?_ ?_ ?_
    · exact hxM
    · exact ⟨⟨hxM, hfN⟩, ⟨hxΩ, mem_univ _⟩⟩
    · exact IsManifold.chart_mem_maximalAtlas (I := I) (n := r) x
    · have heProd : eProd ∈ IsManifold.maximalAtlas (I.prod J) r (M × N) :=
        IsManifold.mem_maximalAtlas_prod
          (IsManifold.chart_mem_maximalAtlas (I := I) (n := r) x)
          (IsManifold.chart_mem_maximalAtlas (I := J) (n := r) (f x))
      have hτg : τ ∈ contDiffGroupoid r (I.prod J) :=
        graphShearPartialOnGeneral_mem_contDiffGroupoid
          (I := I) (J := J) g Ω hΩopen hgOn
      have hτ : ContMDiffOn (I.prod J) (I.prod J) r τ τ.source :=
        contMDiffOn_of_mem_contDiffGroupoid hτg
      have hτsymm : ContMDiffOn (I.prod J) (I.prod J) r τ.symm τ.target :=
        contMDiffOn_of_mem_contDiffGroupoid
          (StructureGroupoid.symm (contDiffGroupoid r (I.prod J)) hτg)
      refine eCod.mem_maximalAtlas_of_contMDiffOn (I := I.prod J) (n := r) ?_ ?_
      · have hProd := contMDiffOn_of_mem_maximalAtlas (I := I.prod J) (n := r) heProd
        rw [OpenPartialHomeomorph.trans_source]
        exact hτ.comp' hProd
      · have hProd := contMDiffOn_symm_of_mem_maximalAtlas (I := I.prod J) (n := r) heProd
        rw [OpenPartialHomeomorph.trans_target]
        exact hProd.comp' hτsymm
    · intro u hu
      set x' : M := (eM.extend I).symm u
      have hx'M : x' ∈ eM.source := by
        have hxSource : (eM.extend I).symm u ∈ (eM.extend I).source :=
          (eM.extend I).map_target hu
        simpa [OpenPartialHomeomorph.extend, x'] using hxSource
      have huM : I (eM x') = u := by
        have := (eM.extend I).right_inv hu
        simpa [OpenPartialHomeomorph.extend, x'] using this
      have hcod :
          eCod (x', f x') =
            (eM x', J.symm (J (eN (f x')) - g (I (eM x')))) := by
        change τ (eProd (x', f x')) = _
        change τ (eM x', eN (f x')) = _
        rfl
      have hgEq : g (I (eM x')) = J (eN (f x')) := by
        simp [g, writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend]
        rw [eM.left_inv hx'M]
      have h0 : J (J.symm (J (eN (f x')) - g (I (eM x')))) = 0 := by
        rw [J.right_inv (by rw [J.range_eq_univ]; exact mem_univ _), hgEq, sub_self]
      simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe]
      rw [hcod, modelWithCorners_prod_coe]
      refine Prod.ext ?_ ?_
      · simpa [ContinuousLinearEquiv.refl_apply] using huM
      · simpa [ContinuousLinearEquiv.refl_apply] using h0
  · exact isEmbedding_graph hf.continuous

end
