import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Sets.Opens
import LeeSmoothLib.Ch05.Sec05_31.Definition_5_31_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped Manifold
open Set Function Topology

universe u𝕜 uE uH uM

namespace Manifold
namespace ImmersedSubmanifold

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- Restricting two compatible maximal-atlas charts to the same open subtype preserves their
transition-map regularity. -/
private lemma proposition522_trans_restricted_mem_contDiffGroupoid
    {E₀ H₀ X : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    [TopologicalSpace H₀] [TopologicalSpace X] [ChartedSpace H₀ X]
    {J : ModelWithCorners 𝕜 E₀ H₀} [IsManifold J (⊤ : WithTop ℕ∞) X]
    {e e' : OpenPartialHomeomorph X H₀}
    (he : e ∈ IsManifold.maximalAtlas J (⊤ : WithTop ℕ∞) X)
    (he' : e' ∈ IsManifold.maximalAtlas J (⊤ : WithTop ℕ∞) X)
    {U : Opens X} (hU : Nonempty U) :
    (e.subtypeRestr hU).symm ≫ₕ e'.subtypeRestr hU ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) J :=
  (contDiffGroupoid (⊤ : WithTop ℕ∞) J).mem_of_eqOnSource
    (closedUnderRestriction'
      ((contDiffGroupoid (⊤ : WithTop ℕ∞) J).compatible_of_mem_maximalAtlas he he')
      (e.isOpen_inter_preimage_symm U.2))
    (e.subtypeRestr_symm_trans_subtypeRestr hU e')

/-- A maximal-atlas chart restricts to a maximal-atlas chart on an open subtype. -/
private lemma proposition522_subtypeRestr_mem_maximalAtlas
    {E₀ H₀ X : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    [TopologicalSpace H₀] [TopologicalSpace X] [ChartedSpace H₀ X]
    {J : ModelWithCorners 𝕜 E₀ H₀} [IsManifold J (⊤ : WithTop ℕ∞) X]
    {e : OpenPartialHomeomorph X H₀}
    (he : e ∈ IsManifold.maximalAtlas J (⊤ : WithTop ℕ∞) X)
    {U : Opens X} (hU : Nonempty U) :
    e.subtypeRestr hU ∈ IsManifold.maximalAtlas J (⊤ : WithTop ℕ∞) U := by
  intro e' he'
  obtain ⟨x, hx⟩ := Opens.chart_eq hU he'
  rw [hx]
  exact ⟨proposition522_trans_restricted_mem_contDiffGroupoid he
      (IsManifold.subset_maximalAtlas (chart_mem_atlas H₀ (x : X))) hU,
    proposition522_trans_restricted_mem_contDiffGroupoid
      (IsManifold.subset_maximalAtlas (chart_mem_atlas H₀ (x : X))) he hU⟩

/-- An extended chart, restricted to its source, is a topological embedding. -/
private lemma proposition522_isEmbedding_extend_subtypeVal
    {E₀ H₀ X : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    [TopologicalSpace H₀] [TopologicalSpace X]
    (J : ModelWithCorners 𝕜 E₀ H₀) (e : OpenPartialHomeomorph X H₀) :
    IsEmbedding (fun x : e.source ↦ (e.extend J) (x : X)) := by
  have hJ : IsEmbedding (J : H₀ → E₀) := J.isClosedEmbedding.isEmbedding
  have hval : IsEmbedding (Subtype.val : e.target → H₀) := IsEmbedding.subtypeVal
  have hhome : IsEmbedding e.toHomeomorphSourceTarget :=
    e.toHomeomorphSourceTarget.isEmbedding
  have hcomp : IsEmbedding (J ∘ Subtype.val ∘ e.toHomeomorphSourceTarget) :=
    hJ.comp (hval.comp hhome)
  convert hcomp using 1
  ext x
  simp [OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe]

/-- The linear normal-form inclusion `x ↦ equiv (x, 0)` is an embedding. -/
private lemma proposition522_isEmbedding_equiv_prod_zero
    {E₀ E₁ F : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (equiv : (E₀ × F) ≃L[𝕜] E₁) :
    IsEmbedding (fun x : E₀ ↦ equiv (x, (0 : F))) :=
  equiv.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft (0 : F))

/-- Evaluate the immersion normal form at a point of its source chart. -/
private lemma proposition522_writtenInCharts_apply
    {E₀ E₁ H₀ H₁ X Y : Type*}
    [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [TopologicalSpace H₀] [TopologicalSpace H₁]
    [TopologicalSpace X] [ChartedSpace H₀ X]
    [TopologicalSpace Y] [ChartedSpace H₁ Y]
    {J : ModelWithCorners 𝕜 E₀ H₀} {K : ModelWithCorners 𝕜 E₁ H₁}
    {f : X → Y} {x : X}
    (h : IsImmersionAt J K (⊤ : WithTop ℕ∞) f x)
    {y : X} (hy : y ∈ h.domChart.source) :
    (h.codChart.extend K) (f y) = h.equiv (h.domChart.extend J y, 0) := by
  have hy' : h.domChart.extend J y ∈ (h.domChart.extend J).target :=
    (h.domChart.extend J).map_source (by rwa [OpenPartialHomeomorph.extend_source])
  have hEq := h.writtenInCharts hy'
  dsimp [Function.comp, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm] at hEq ⊢
  rwa [J.left_inv, h.domChart.left_inv hy] at hEq

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement
-- surface was verified against the local `Theorem_4_25` and `ImmersedSubmanifold` APIs.
/-- Proposition 5.22 (Immersed Submanifolds Are Locally Embedded): for each point `p` of an
immersed submanifold `S` of `M`, there is an open neighborhood `U` of `p` in `S` such that the
restricted inclusion `U → M` is a smooth embedding. Hence `U` is an embedded submanifold of `M`
in the source sense. -/
theorem exists_open_neighborhood_isSmoothEmbedding (S : ImmersedSubmanifold I M) (p : S) :
    ∃ U : Opens S, p ∈ U ∧
      IsSmoothEmbedding (modelWithCornersSelf 𝕜 S.ModelSpace) I (⊤ : WithTop ℕ∞)
        (S.inclusion ∘ (Subtype.val : U → S)) := by
  let hp := S.inclusion_isImmersion.isImmersionAt p
  let U : Opens S := ⟨hp.domChart.source, hp.domChart.open_source⟩
  refine ⟨U, hp.mem_domChart_source, ?_, ?_⟩
  · -- The same immersion normal form restricts to the source chart domain.
    refine ⟨hp.complement, inferInstance, inferInstance, ?_⟩
    intro q
    have hU : Nonempty U := ⟨q⟩
    refine IsImmersionAtOfComplement.mk_of_charts hp.equiv
      (hp.domChart.subtypeRestr hU) hp.codChart ?_ ?_ ?_ ?_ ?_ ?_
    · simp [OpenPartialHomeomorph.subtypeRestr_source, U]
    · exact hp.source_subset_preimage_source q.property
    · exact proposition522_subtypeRestr_mem_maximalAtlas hp.domChart_mem_maximalAtlas hU
    · exact hp.codChart_mem_maximalAtlas
    · intro x _hx
      exact hp.source_subset_preimage_source x.property
    · intro y hy
      rw [OpenPartialHomeomorph.extend_target] at hy
      have hyU :
          (modelWithCornersSelf 𝕜 S.ModelSpace).symm y ∈
            (hp.domChart.subtypeRestr hU).target := hy.1
      have hyrange : y ∈ Set.range (modelWithCornersSelf 𝕜 S.ModelSpace) := hy.2
      have hye :
          (modelWithCornersSelf 𝕜 S.ModelSpace).symm y ∈ hp.domChart.target :=
        hp.domChart.subtypeRestr_target_subset hU hyU
      have hytarget :
          y ∈ (hp.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).target := by
        rw [OpenPartialHomeomorph.extend_target]
        exact ⟨hye, hyrange⟩
      have hsrc :
          (hp.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).symm y ∈
            hp.domChart.source := by
        simpa [OpenPartialHomeomorph.extend_source] using
          (hp.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).map_target hytarget
      have happly := proposition522_writtenInCharts_apply hp hsrc
      have hright :
          hp.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)
              ((hp.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).symm y) = y :=
        (hp.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).right_inv hytarget
      have hval :
          ((hp.domChart.subtypeRestr hU).symm
              ((modelWithCornersSelf 𝕜 S.ModelSpace).symm y) : S) =
            hp.domChart.symm ((modelWithCornersSelf 𝕜 S.ModelSpace).symm y) :=
        hp.domChart.subtypeRestr_symm_apply hU hyU
      have hval' :
          ((hp.domChart.subtypeRestr hU).symm y : S) = hp.domChart.symm y := by
        simpa using hval
      dsimp [Function.comp, OpenPartialHomeomorph.extend_coe,
        OpenPartialHomeomorph.extend_coe_symm] at happly hright ⊢
      rw [hval', happly, hright]
  · -- In the same normal form, the restriction is a composition of topological embeddings.
    let F_to_cod : U → hp.codChart.source := fun x ↦
      ⟨S.inclusion x.val, hp.source_subset_preimage_source x.property⟩
    have hcod : IsEmbedding
        (fun t : hp.codChart.source ↦ (hp.codChart.extend I) (t : M)) :=
      proposition522_isEmbedding_extend_subtypeVal I hp.codChart
    have hdom : IsEmbedding
        (fun x : hp.domChart.source ↦
          (hp.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) (x : S)) :=
      proposition522_isEmbedding_extend_subtypeVal
        (modelWithCornersSelf 𝕜 S.ModelSpace) hp.domChart
    have hlin : IsEmbedding
        (fun x : S.ModelSpace ↦ hp.equiv (x, (0 : hp.complement))) :=
      proposition522_isEmbedding_equiv_prod_zero hp.equiv
    have hcomp : IsEmbedding
        ((fun t : hp.codChart.source ↦ (hp.codChart.extend I) (t : M)) ∘ F_to_cod) := by
      have heq :
          (fun t : hp.codChart.source ↦ (hp.codChart.extend I) (t : M)) ∘ F_to_cod =
            (fun x : S.ModelSpace ↦ hp.equiv (x, (0 : hp.complement))) ∘
              (fun x : hp.domChart.source ↦
                (hp.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) (x : S)) := by
        ext x
        exact proposition522_writtenInCharts_apply hp x.property
      rw [heq]
      exact hlin.comp hdom
    have hF_to_cod : IsEmbedding F_to_cod := (IsEmbedding.of_comp_iff hcod).1 hcomp
    have hval : (S.inclusion ∘ Subtype.val : U → M) = Subtype.val ∘ F_to_cod := rfl
    rw [hval]
    exact IsEmbedding.subtypeVal.comp hF_to_cod

end

end ImmersedSubmanifold
end Manifold
