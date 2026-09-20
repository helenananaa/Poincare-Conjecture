import Mathlib.Geometry.Manifold.SmoothEmbedding

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff Topology
open Manifold

universe u𝕜 uE uH uM uE' uH' uN

noncomputable section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (∞ : ℕ∞ω) M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J (∞ : ℕ∞ω) N]

/-- A charted-space structure on `Set.range F` is adapted to `F` if it makes the image into a
smooth manifold for which the subtype inclusion is a smooth embedding and `F` becomes a
diffeomorphism onto its image. -/
def IsInducedImageManifoldStructure (F : N → M) (cs : ChartedSpace H' (Set.range F)) : Prop :=
  let _ : ChartedSpace H' (Set.range F) := cs
  ∃ (_im : IsManifold J (∞ : ℕ∞ω) (Set.range F)),
    let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := _im
    Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : Set.range F → M) ∧
      ∃ Φ : N ≃ₘ⟮J, J⟯ Set.range F, ∀ x, (Φ x : M) = F x

/-- Transport the source atlas of `N` to `Set.range F` through the embedding homeomorphism. -/
private noncomputable abbrev transported_range_chartedSpace {F : N → M}
    (e : N ≃ₜ Set.range F) : ChartedSpace H' (Set.range F) := by
  let _ : ChartedSpace N (Set.range F) :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  exact ChartedSpace.comp H' N (Set.range F)

/-- The transported range charted space is a smooth manifold at regularity `∞`. -/
lemma transported_range_isManifold {F : N → M} (e : N ≃ₜ Set.range F) :
    let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
    IsManifold J (∞ : ℕ∞ω) (Set.range F) := by
  let eS : OpenPartialHomeomorph (Set.range F) N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N (Set.range F) := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
  have hGroupoid : HasGroupoid (Set.range F) (contDiffGroupoid (∞ : ℕ∞ω) J) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) f hf
    have hf'Eq : f' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈ contDiffGroupoid (∞ : ℕ∞ω) J := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible (G := contDiffGroupoid (∞ : ℕ∞ω) J) hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  exact IsManifold.mk' J (∞ : ℕ∞ω) (Set.range F)

/-- The transporting homeomorphism is smooth for the singleton-chart atlas on the image. -/
lemma transported_range_homeomorph_contMDiff {F : N → M} (e : N ≃ₜ Set.range F) :
    let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
    let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := transported_range_isManifold e
    ContMDiff J J (∞ : ℕ∞ω) e := by
  let eS : OpenPartialHomeomorph (Set.range F) N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N (Set.range F) := eS.singletonChartedSpace (by
    ext z
    simp [eS])
  let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
  let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := transported_range_isManifold e
  change ContMDiff J J (∞ : ℕ∞ω) e
  intro x
  rw [contMDiffAt_iff]
  constructor
  · exact e.continuous.continuousAt
  · have hchart : chartAt N (e x) = eS :=
      eS.singletonChartedSpace_chartAt_eq (by
        ext z
        simp [eS])
    have hpoint : eS (e x) = x := by
      simp [eS]
    have hcenter :
        letI := ChartedSpace.comp H' N (Set.range F)
        extChartAt J (e x) (e x) = extChartAt J x x := by
      simp [chartAt_comp, hpoint]
    have hcenterChart :
        letI := ChartedSpace.comp H' N (Set.range F)
        chartAt H' (e x) (e x) = chartAt H' x x := by
      simp [chartAt_comp, hpoint, OpenPartialHomeomorph.trans_apply]
    refine
      (contDiffWithinAt_id :
        ContDiffWithinAt 𝕜 ∞ (id : E' → E') (Set.range J) (extChartAt J x x)).congr_of_eventuallyEq_of_mem
        ?_ ?_
    · have htarget :
          letI := ChartedSpace.comp H' N (Set.range F)
          (extChartAt J (e x)).target ∈ nhdsWithin (extChartAt J x x) (Set.range J) := by
        have htarget' :
            letI := ChartedSpace.comp H' N (Set.range F)
            (extChartAt J (e x)).target ∈
              nhdsWithin (extChartAt J (e x) (e x)) (Set.range J) :=
          extChartAt_target_mem_nhdsWithin (e x)
        simpa [hcenter, hcenterChart] using htarget'
      filter_upwards [htarget] with y hy
      simpa [hchart, hpoint, eS, chartAt_comp, extChartAt_comp, Function.comp,
        OpenPartialHomeomorph.trans_apply] using
        (writtenInExtChartAt_chartAt_symm_comp (e x) hy)
    · exact Set.mem_of_subset_of_mem (extChartAt_target_subset_range x)
        (mem_extChartAt_target x)

/-- The inverse of the transporting homeomorphism is smooth for the transported atlas. -/
lemma transported_range_homeomorph_symm_contMDiff {F : N → M} (e : N ≃ₜ Set.range F) :
    let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
    let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := transported_range_isManifold e
    ContMDiff J J (∞ : ℕ∞ω) e.symm := by
  let eS : OpenPartialHomeomorph (Set.range F) N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N (Set.range F) := eS.singletonChartedSpace (by
    ext z
    simp [eS])
  let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
  let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := transported_range_isManifold e
  change ContMDiff J J (∞ : ℕ∞ω) e.symm
  intro x
  rw [contMDiffAt_iff]
  constructor
  · exact e.symm.continuous.continuousAt
  · have hchart : chartAt N x = eS :=
      eS.singletonChartedSpace_chartAt_eq (by
        ext z
        simp [eS])
    refine
      (contDiffWithinAt_id :
        ContDiffWithinAt 𝕜 ∞ (id : E' → E') (Set.range J)
          (extChartAt J x x)).congr_of_eventuallyEq_of_mem ?_ ?_
    · filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
      simpa [hchart, eS, chartAt_comp, extChartAt_comp, Function.comp,
        OpenPartialHomeomorph.trans_apply] using
        (writtenInExtChartAt_chartAt_comp x hy)
    · exact Set.mem_of_subset_of_mem (extChartAt_target_subset_range (e.symm x))
        (mem_extChartAt_target (e.symm x))

/-- Package the transporting homeomorphism as a diffeomorphism of the image. -/
noncomputable def transported_range_diffeomorph {F : N → M} (e : N ≃ₜ Set.range F) :
    let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
    let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := transported_range_isManifold e
    N ≃ₘ⟮J, J⟯ Set.range F := by
  let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
  let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := transported_range_isManifold e
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := transported_range_homeomorph_contMDiff e
      contMDiff_invFun := transported_range_homeomorph_symm_contMDiff e }

omit [IsManifold I (∞ : ℕ∞ω) M] in
/-- After transporting charts across the embedding homeomorphism, the subtype inclusion remains
an immersion. -/
lemma transported_range_subtype_val_isImmersion {F : N → M}
    (hF : IsSmoothEmbedding J I (∞ : ℕ∞ω) F) (e : N ≃ₜ Set.range F)
    (he : ∀ x, (e x : M) = F x) :
    let _ : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
    let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := transported_range_isManifold e
    IsImmersion J I (∞ : ℕ∞ω) (Subtype.val : Set.range F → M) := by
  let instCharted : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
  let _ : ChartedSpace H' (Set.range F) := instCharted
  let instManifold : IsManifold J (∞ : ℕ∞ω) (Set.range F) := transported_range_isManifold e
  let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := instManifold
  let hImm := hF.isImmersion
  let hCompImm := hImm.isImmersionOfComplement_complement
  let eS : OpenPartialHomeomorph (Set.range F) N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N (Set.range F) := eS.singletonChartedSpace (by
    ext z
    simp [eS])
  refine ⟨hImm.complement, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm (e.symm x)
  refine IsImmersionAtOfComplement.mk_of_charts
    hx.equiv (eS.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [eS, OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
  · have hxe : F (e.symm x) = (x : M) := by
      simpa using (he (e.symm x)).symm
    simpa [hxe] using hx.mem_codChart_source
  · intro d hd
    rcases hd with ⟨f, hf, c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext z
        simp [eS]) f hf
    subst f
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    constructor
    · have hleft :
          ((hx.domChart.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
            contDiffGroupoid (∞ : ℕ∞ω) J := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').1
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hleft
    · have hright :
          ((c'.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ hx.domChart) ∈
            contDiffGroupoid (∞ : ℕ∞ω) J := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').2
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hright
  · exact hx.codChart_mem_maximalAtlas
  · intro z hz
    have hz' : e.symm z ∈ hx.domChart.source := by
      simpa [eS, OpenPartialHomeomorph.trans_source] using hz
    have hze : F (e.symm z) = (z : M) := by
      simpa using (he (e.symm z)).symm
    simpa [hze] using hx.source_subset_preimage_source hz'
  · intro u hu
    have hu' : u ∈ (hx.domChart.extend J).target := by
      simpa [eS, OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
    have hpoint :
        ((e (hx.domChart.symm (J.symm u)) : Set.range F) : M) =
          F (hx.domChart.symm (J.symm u)) :=
      he (hx.domChart.symm (J.symm u))
    simpa [eS, Function.comp, OpenPartialHomeomorph.extend_coe_symm,
      OpenPartialHomeomorph.extend_coe, hpoint] using hx.writtenInCharts hu'

omit [IsManifold I (∞ : ℕ∞ω) M] in
/-- Proposition 5.2: the image of a smooth embedding inherits a smooth manifold structure with the
subspace topology for which the subtype inclusion is a smooth embedding and the original map is a
diffeomorphism onto its image. -/
-- Proof sketch: the topological embedding part of `hF` gives a homeomorphism
-- `N ≃ₜ Set.range F`; transport the charted-space and smooth-manifold structures of `N` across
-- this homeomorphism. Under the transported structure, the induced map `N → Set.range F` is a
-- diffeomorphism by construction, and composing it with `Subtype.val` recovers `F`, so the
-- subtype inclusion is a smooth embedding.
theorem smooth_embedding_range_has_induced_manifold_structure {F : N → M}
    (hF : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) F) :
    ∃ cs : ChartedSpace H' (Set.range F),
      @IsInducedImageManifoldStructure 𝕜 _ E _ _ H _ M _ _ I E' _ _ H' _ J N _ _ F cs := by
  let e : N ≃ₜ Set.range F := hF.isEmbedding.toHomeomorph
  let cs : ChartedSpace H' (Set.range F) := transported_range_chartedSpace e
  refine ⟨cs, ?_⟩
  let _ : ChartedSpace H' (Set.range F) := cs
  refine ⟨transported_range_isManifold e, ?_⟩
  let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := transported_range_isManifold e
  have he : ∀ x, (e x : M) = F x := by
    intro x
    simp [e]
  have hSubtype : IsSmoothEmbedding J I (∞ : ℕ∞ω)
      (Subtype.val : Set.range F → M) :=
    ⟨transported_range_subtype_val_isImmersion hF e he, Topology.IsEmbedding.subtypeVal⟩
  refine ⟨hSubtype, ?_⟩
  refine ⟨transported_range_diffeomorph e, ?_⟩
  intro x
  change ((e x : Set.range F) : M) = F x
  exact he x

omit [IsManifold I (∞ : ℕ∞ω) M] [IsManifold J (∞ : ℕ∞ω) N] in
/-- Two diffeomorphisms from `N` onto the same image manifold structure that both realize `F` agree
pointwise, hence are equal. -/
-- Proof sketch: for each `x : N`, the equalities in `M` force the corresponding points of
-- `Set.range F` to coincide because `Subtype.val` is injective. Then apply extensionality for
-- diffeomorphisms.
theorem image_diffeomorph_eq_of_comp_subtype_val {F : N → M}
    [ChartedSpace H' (Set.range F)] [IsManifold J (∞ : ℕ∞ω) (Set.range F)]
    {Φ Ψ : N ≃ₘ⟮J, J⟯ Set.range F}
    (hΦ : ∀ x, (Φ x : M) = F x) (hΨ : ∀ x, (Ψ x : M) = F x) :
    Φ = Ψ := by
  apply Diffeomorph.ext
  intro x
  exact Subtype.ext (hΦ x ▸ (hΨ x).symm)

end
