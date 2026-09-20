import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so local chapter
-- precedents and mathlib's `Manifold.IsImmersion` / `Manifold.IsSmoothEmbedding` APIs were
-- inspected directly.

open scoped ContDiff Manifold
open Set Function Topology

set_option linter.unusedSectionVars false

namespace Manifold

section

universe uE uE' uH uH' uM uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Transition maps of `subtypeRestr` of maximal-atlas charts remain in the `C^∞` groupoid. -/
lemma trans_restricted_mem_contDiffGroupoid_of_mem_maximalAtlas
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    {s : TopologicalSpace.Opens M} (hs : Nonempty s) :
    (e.subtypeRestr hs).symm ≫ₕ e'.subtypeRestr hs ∈ contDiffGroupoid ∞ I :=
  (contDiffGroupoid ∞ I).mem_of_eqOnSource
    (closedUnderRestriction'
      ((contDiffGroupoid ∞ I).compatible_of_mem_maximalAtlas he he')
      (e.isOpen_inter_preimage_symm s.2))
    (e.subtypeRestr_symm_trans_subtypeRestr hs e')

/-- Restricting a maximal-atlas chart of `M` to an open subset yields a maximal-atlas chart of
that subset. -/
lemma subtypeRestr_mem_maximalAtlas_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {s : TopologicalSpace.Opens M} (hs : Nonempty s) :
    e.subtypeRestr hs ∈ IsManifold.maximalAtlas I ∞ s := by
  intro e' he'
  obtain ⟨x, hx⟩ := TopologicalSpace.Opens.chart_eq hs he'
  rw [hx]
  exact ⟨trans_restricted_mem_contDiffGroupoid_of_mem_maximalAtlas he
      (IsManifold.subset_maximalAtlas (chart_mem_atlas H (x : M))) hs,
    trans_restricted_mem_contDiffGroupoid_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (chart_mem_atlas H (x : M))) he hs⟩

/-- The extended chart of an open partial homeomorphism is a topological embedding on its
source. -/
lemma isEmbedding_extend_subtypeVal (e : OpenPartialHomeomorph M H) :
    IsEmbedding (fun x : e.source ↦ (e.extend I) (x : M)) := by
  have hI : IsEmbedding (I : H → E) := I.isClosedEmbedding.isEmbedding
  have hval : IsEmbedding (Subtype.val : e.target → H) := IsEmbedding.subtypeVal
  have hhome : IsEmbedding e.toHomeomorphSourceTarget :=
    e.toHomeomorphSourceTarget.isEmbedding
  have hcomp : IsEmbedding (I ∘ Subtype.val ∘ e.toHomeomorphSourceTarget) :=
    hI.comp (hval.comp hhome)
  convert hcomp using 1
  ext x
  simp [OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe]

/-- The model inclusion `x ↦ equiv (x, 0)` is a topological embedding. -/
lemma isEmbedding_equiv_prod_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (equiv : (E × F) ≃L[ℝ] E') :
    IsEmbedding (fun x : E ↦ equiv (x, (0 : F))) :=
  equiv.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft (0 : F))

/-- Evaluating the immersion normal form at a source point. -/
lemma IsImmersionAt.writtenInCharts_apply {f : M → N} {x : M}
    (h : IsImmersionAt I J ∞ f x) {y : M} (hy : y ∈ h.domChart.source) :
    (h.codChart.extend J) (f y) = h.equiv (h.domChart.extend I y, 0) := by
  have hy' : h.domChart.extend I y ∈ (h.domChart.extend I).target :=
    (h.domChart.extend I).map_source (by rwa [OpenPartialHomeomorph.extend_source])
  have hEq := h.writtenInCharts hy'
  dsimp [Function.comp, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm] at hEq ⊢
  rwa [I.left_inv, h.domChart.left_inv hy] at hEq

/-- Restricting an immersion to one of its domain-chart sources yields an immersion. -/
lemma isImmersion_restrict_domChart {f : M → N} {p : M} (hf : IsImmersionAt I J ∞ f p) :
    IsImmersion I J ∞
      (f ∘ Subtype.val :
        (⟨hf.domChart.source, hf.domChart.open_source⟩ : TopologicalSpace.Opens M) → N) := by
  set U : TopologicalSpace.Opens M := ⟨hf.domChart.source, hf.domChart.open_source⟩
  refine ⟨hf.complement, inferInstance, inferInstance, ?_⟩
  intro q
  have hU : Nonempty U := ⟨q⟩
  refine IsImmersionAtOfComplement.mk_of_charts hf.equiv
    (hf.domChart.subtypeRestr hU) hf.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · simp [OpenPartialHomeomorph.subtypeRestr_source, U]
  · exact hf.source_subset_preimage_source q.property
  · exact subtypeRestr_mem_maximalAtlas_of_mem_maximalAtlas hf.domChart_mem_maximalAtlas hU
  · exact hf.codChart_mem_maximalAtlas
  · intro x _hx
    exact hf.source_subset_preimage_source x.property
  · intro y hy
    rw [OpenPartialHomeomorph.extend_target] at hy
    have hy_eU : I.symm y ∈ (hf.domChart.subtypeRestr hU).target := hy.1
    have hy_range : y ∈ range (I : H → E) := hy.2
    have hy_e : I.symm y ∈ hf.domChart.target :=
      hf.domChart.subtypeRestr_target_subset hU hy_eU
    have hy_target : y ∈ (hf.domChart.extend I).target := by
      rw [OpenPartialHomeomorph.extend_target]
      exact ⟨hy_e, hy_range⟩
    have hsrc : (hf.domChart.extend I).symm y ∈ hf.domChart.source := by
      simpa [OpenPartialHomeomorph.extend_source] using
        (hf.domChart.extend I).map_target hy_target
    have happly := hf.writtenInCharts_apply hsrc
    have hright : hf.domChart.extend I ((hf.domChart.extend I).symm y) = y :=
      (hf.domChart.extend I).right_inv hy_target
    have hval' : ((hf.domChart.subtypeRestr hU).symm (I.symm y) : M) =
        hf.domChart.symm (I.symm y) :=
      hf.domChart.subtypeRestr_symm_apply (U := U) hU hy_eU
    dsimp [Function.comp, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm] at happly hright ⊢
    rw [hval', happly, hright]

/-- Restricting an immersion to one of its domain-chart sources yields a topological embedding. -/
lemma isEmbedding_restrict_domChart {f : M → N} {p : M} (hf : IsImmersionAt I J ∞ f p) :
    IsEmbedding
      (f ∘ Subtype.val :
        (⟨hf.domChart.source, hf.domChart.open_source⟩ : TopologicalSpace.Opens M) → N) := by
  set U : TopologicalSpace.Opens M := ⟨hf.domChart.source, hf.domChart.open_source⟩
  let F_to_cod : U → hf.codChart.source := fun x ↦
    ⟨f x.val, hf.source_subset_preimage_source x.property⟩
  have hT_emb : IsEmbedding (fun t : hf.codChart.source ↦ (hf.codChart.extend J) (t : N)) :=
    isEmbedding_extend_subtypeVal (I := J) hf.codChart
  have hU_emb : IsEmbedding (fun x : hf.domChart.source ↦ (hf.domChart.extend I) (x : M)) :=
    isEmbedding_extend_subtypeVal (I := I) hf.domChart
  have hι : IsEmbedding (fun x : E ↦ hf.equiv (x, (0 : hf.complement))) :=
    isEmbedding_equiv_prod_zero hf.equiv
  have hcomp : IsEmbedding
      ((fun t : hf.codChart.source ↦ (hf.codChart.extend J) (t : N)) ∘ F_to_cod) := by
    have hEq : (fun t : hf.codChart.source ↦ (hf.codChart.extend J) (t : N)) ∘ F_to_cod =
        (fun x : E ↦ hf.equiv (x, (0 : hf.complement))) ∘
          (fun x : hf.domChart.source ↦ (hf.domChart.extend I) (x : M)) := by
      ext x
      exact hf.writtenInCharts_apply x.property
    rw [hEq]
    exact hι.comp hU_emb
  have hF_to_cod : IsEmbedding F_to_cod := (IsEmbedding.of_comp_iff hT_emb).1 hcomp
  have hval : (f ∘ Subtype.val : U → N) = Subtype.val ∘ F_to_cod := rfl
  rw [hval]
  exact IsEmbedding.subtypeVal.comp hF_to_cod

/-- Lifting a maximal-atlas chart of an open subset along the open inclusion recovers a
maximal-atlas chart of `M`. -/
lemma lift_openEmbedding_subtypeVal_mem_maximalAtlas
    {U : TopologicalSpace.Opens M} (hU : Nonempty U) [Nonempty H]
    {e : OpenPartialHomeomorph U H} (he : e ∈ IsManifold.maximalAtlas I ∞ U) :
    e.lift_openEmbedding U.isOpen.isOpenEmbedding_subtypeVal ∈
      IsManifold.maximalAtlas I ∞ M := by
  intro c hc
  let cU : OpenPartialHomeomorph U H := c.subtypeRestr hU
  have hcU : cU ∈ IsManifold.maximalAtlas I ∞ U :=
    (contDiffGroupoid ∞ I).subtypeRestr_mem_maximalAtlas hc hU
  let eM := e.lift_openEmbedding U.isOpen.isOpenEmbedding_subtypeVal
  have hι : IsOpenEmbedding (Subtype.val : U → M) := U.isOpen.isOpenEmbedding_subtypeVal
  have hcU_target :
      cU.target = c.target ∩ c.symm ⁻¹' (U : Set M) := by
    simp [cU, OpenPartialHomeomorph.subtypeRestr_def,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  have hleft : eM.symm.trans c ≈ e.symm.trans cU := by
    refine ⟨?_, ?_⟩
    · ext y
      change (y ∈ eM.target ∧ eM.symm y ∈ c.source) ↔
        (y ∈ e.target ∧ e.symm y ∈ cU.source)
      simp [eM, cU, OpenPartialHomeomorph.lift_openEmbedding_target,
        OpenPartialHomeomorph.lift_openEmbedding_symm,
        OpenPartialHomeomorph.subtypeRestr_source]
    · intro y _hy
      change c (eM.symm y) = cU (e.symm y)
      simp [eM, cU, OpenPartialHomeomorph.lift_openEmbedding_symm,
        OpenPartialHomeomorph.subtypeRestr_coe, Set.restrict_apply]
  have hright : c.symm.trans eM ≈ cU.symm.trans e := by
    refine ⟨?_, ?_⟩
    · ext y
      constructor
      · intro hy
        have hy_tgt : y ∈ c.target := hy.1
        have hy_src : c.symm y ∈ eM.source := hy.2
        have hy_img : c.symm y ∈ (↑) '' e.source := by
          simpa [eM] using hy_src
        rcases hy_img with ⟨z, hz, hzy⟩
        have hy_U : c.symm y ∈ (U : Set M) := by
          rw [← hzy]
          exact z.property
        have hy_cU : y ∈ cU.target := by
          rw [hcU_target]
          exact ⟨hy_tgt, hy_U⟩
        have hval : (cU.symm y : M) = c.symm y :=
          c.subtypeRestr_symm_apply (U := U) hU hy_cU
        have hz' : cU.symm y ∈ e.source := by
          have : (cU.symm y : M) = (z : M) := hval.trans hzy.symm
          exact (Subtype.ext this).symm ▸ hz
        exact ⟨hy_cU, hz'⟩
      · intro hy
        have hy_cU : y ∈ cU.target := hy.1
        have hy_e : cU.symm y ∈ e.source := hy.2
        have hy_tgt : y ∈ c.target := c.subtypeRestr_target_subset hU hy_cU
        have hval : (cU.symm y : M) = c.symm y :=
          c.subtypeRestr_symm_apply (U := U) hU hy_cU
        have : c.symm y ∈ eM.source := by
          simp only [eM, OpenPartialHomeomorph.lift_openEmbedding_source]
          exact ⟨cU.symm y, hy_e, hval⟩
        exact ⟨hy_tgt, this⟩
    · intro y hy
      change eM (c.symm y) = e (cU.symm y)
      have hy_tgt : y ∈ c.target := hy.1
      have hy_img : c.symm y ∈ (↑) '' e.source := by
        simpa [eM] using hy.2
      rcases hy_img with ⟨z, hz, hzy⟩
      have hy_U : c.symm y ∈ (U : Set M) := by
        rw [← hzy]
        exact z.property
      have hy_cU : y ∈ cU.target := by
        rw [hcU_target]
        exact ⟨hy_tgt, hy_U⟩
      have hval : (cU.symm y : M) = c.symm y :=
        c.subtypeRestr_symm_apply (U := U) hU hy_cU
      have happly := e.lift_openEmbedding_apply hι (x := cU.symm y)
      rw [← hval]
      exact happly
  exact ⟨(contDiffGroupoid ∞ I).mem_of_eqOnSource
      ((contDiffGroupoid ∞ I).compatible_of_mem_maximalAtlas he hcU) hleft,
    (contDiffGroupoid ∞ I).mem_of_eqOnSource
      ((contDiffGroupoid ∞ I).compatible_of_mem_maximalAtlas hcU he) hright⟩

/-- An immersion of an open restriction lifts to an immersion of the original map at the same
point. -/
lemma isImmersionAtOfComplement_of_restriction
    {U : TopologicalSpace.Opens M} {p : M} (hp : p ∈ U) {f : M → N}
    {Fspace : Type*} [NormedAddCommGroup Fspace] [NormedSpace ℝ Fspace]
    (h : IsImmersionAtOfComplement Fspace I J ∞
      (f ∘ Subtype.val : U → N) ⟨p, hp⟩) :
    IsImmersionAtOfComplement Fspace I J ∞ f p := by
  haveI : Nonempty U := ⟨⟨p, hp⟩⟩
  haveI : Nonempty H := ⟨h.domChart ⟨p, hp⟩⟩
  have hp_source : (⟨p, hp⟩ : U) ∈ h.domChart.source := h.mem_domChart_source
  set eM := h.domChart.lift_openEmbedding U.isOpen.isOpenEmbedding_subtypeVal
  refine IsImmersionAtOfComplement.mk_of_charts h.equiv eM h.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨⟨p, hp⟩, hp_source, rfl⟩
  · simpa using h.mem_codChart_source
  · exact lift_openEmbedding_subtypeVal_mem_maximalAtlas ⟨⟨p, hp⟩⟩ h.domChart_mem_maximalAtlas
  · exact h.codChart_mem_maximalAtlas
  · intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    exact h.source_subset_preimage_source hz
  · intro y hy
    have hy' : y ∈ (h.domChart.extend I).target := by
      simpa [eM, OpenPartialHomeomorph.extend_target] using hy
    have hEq := h.writtenInCharts hy'
    dsimp [Function.comp, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm] at hEq ⊢
    -- `eM.symm = Subtype.val ∘ h.domChart.symm`
    simpa [eM, OpenPartialHomeomorph.lift_openEmbedding_symm] using hEq

/-- Complements of finite-dimensional immersions satisfy `finrank E + finrank F = finrank E'`. -/
lemma finrank_prod_isImmersion_complement
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {f : X → N} (hf : IsImmersion I J ∞ f) (x : X) :
    Module.finrank ℝ E + Module.finrank ℝ hf.complement = Module.finrank ℝ E' := by
  let e := (hf.isImmersionOfComplement_complement x).equiv
  haveI : FiniteDimensional ℝ (E × hf.complement) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  haveI : FiniteDimensional ℝ hf.complement :=
    FiniteDimensional.of_injective (LinearMap.inr ℝ E hf.complement) LinearMap.inr_injective
  have hsum : Module.finrank ℝ (E × hf.complement) =
      Module.finrank ℝ E + Module.finrank ℝ hf.complement :=
    Module.finrank_prod
  have heq : Module.finrank ℝ (E × hf.complement) = Module.finrank ℝ E' :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  exact hsum.symm.trans heq

lemma finiteDimensional_isImmersion_complement
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {f : X → N} (hf : IsImmersion I J ∞ f) (x : X) :
    FiniteDimensional ℝ hf.complement := by
  let e := (hf.isImmersionOfComplement_complement x).equiv
  haveI : FiniteDimensional ℝ (E × hf.complement) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  exact FiniteDimensional.of_injective (LinearMap.inr ℝ E hf.complement) LinearMap.inr_injective

/-- Theorem 4.25 (Local Embedding Theorem): a smooth map is a smooth immersion if and only if
every point of the source has an open neighborhood on which the restricted map is a smooth
embedding. -/
theorem isImmersion_iff_forall_exists_open_restriction_isSmoothEmbedding {F : M → N} :
    IsImmersion I J ∞ F ↔
      ∀ p : M, ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
        IsSmoothEmbedding I J ∞ (F ∘ (Subtype.val : U → M)) := by
  constructor
  · intro hF p
    let hf := hF.isImmersionAt p
    let U : TopologicalSpace.Opens M := ⟨hf.domChart.source, hf.domChart.open_source⟩
    refine ⟨U, hf.mem_domChart_source, ?_⟩
    exact ⟨isImmersion_restrict_domChart hf, isEmbedding_restrict_domChart hf⟩
  · intro hlocal
    classical
    by_cases hEmpty : IsEmpty M
    · exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ (IsEmpty.false x).elim⟩
    obtain ⟨p0⟩ := not_isEmpty_iff.mp hEmpty
    obtain ⟨U0, hp0, h0emb⟩ := hlocal p0
    let F0 := h0emb.isImmersion.complement
    refine ⟨F0, inferInstance, inferInstance, ?_⟩
    intro p
    obtain ⟨U, hp, hemb⟩ := hlocal p
    haveI := finiteDimensional_isImmersion_complement hemb.isImmersion ⟨p, hp⟩
    haveI := finiteDimensional_isImmersion_complement h0emb.isImmersion ⟨p0, hp0⟩
    have hEq : Module.finrank ℝ hemb.isImmersion.complement = Module.finrank ℝ F0 :=
      Nat.add_left_cancel
        ((finrank_prod_isImmersion_complement hemb.isImmersion ⟨p, hp⟩).trans
          (finrank_prod_isImmersion_complement h0emb.isImmersion ⟨p0, hp0⟩).symm)
    let eF : hemb.isImmersion.complement ≃L[ℝ] F0 := ContinuousLinearEquiv.ofFinrankEq hEq
    have hAt : IsImmersionAtOfComplement F0 I J ∞ (F ∘ Subtype.val : U → N) ⟨p, hp⟩ :=
      (hemb.isImmersion.isImmersionOfComplement_complement ⟨p, hp⟩).trans_F eF
    exact isImmersionAtOfComplement_of_restriction hp hAt

end

end Manifold
