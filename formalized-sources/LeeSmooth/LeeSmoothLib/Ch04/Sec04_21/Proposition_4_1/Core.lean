import Mathlib
import LeeSmoothLib.Ch04.Sec04_24.Theorem_4_25
import LeeSmoothLib.Ch04.Sec04_25.Proposition_4_28

open scoped ContDiff Manifold Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

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

/-- Surjective continuous linear maps with finite-dimensional codomain form an open set. -/
private lemma isOpen_surjective_clm :
    IsOpen {L : E →L[ℝ] E' | Function.Surjective L} := by
  rw [isOpen_iff_eventually]
  intro A hA
  have hRange : A.range = ⊤ := LinearMap.range_eq_top.2 hA
  obtain ⟨B, hB⟩ := ContinuousLinearMap.exists_rightInverse_of_surjective A hRange
  have hCompCont : ContinuousAt (fun L : E →L[ℝ] E' ↦ L.comp B) A :=
    (continuous_id.clm_comp_const B).continuousAt
  have hNear :
      (fun L : E →L[ℝ] E' ↦ L.comp B) ⁻¹'
        Metric.ball (ContinuousLinearMap.id ℝ E') 1 ∈ 𝓝 A := by
    apply hCompCont.preimage_mem_nhds
    simpa [hB] using
      (Metric.ball_mem_nhds (ContinuousLinearMap.id ℝ E') zero_lt_one)
  filter_upwards [hNear] with L hL
  have hDist : ‖ContinuousLinearMap.id ℝ E' - L.comp B‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hL
  have hUnit : IsUnit (L.comp B) := by
    have hCancel :
        ContinuousLinearMap.id ℝ E' -
            (ContinuousLinearMap.id ℝ E' - L.comp B) = L.comp B := by
      ext v
      simp
    exact hCancel ▸ isUnit_one_sub_of_norm_lt_one hDist
  have hCompSurj : Function.Surjective (L.comp B) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hUnit).2
  intro z
  obtain ⟨w, hw⟩ := hCompSurj z
  exact ⟨B w, hw⟩

/-- Injectivity of a manifold derivative is unchanged by the fixed chart-coordinate
identifications used by `inTangentCoordinates`. -/
private lemma injective_mfderiv_iff_inTangentCoordinates
    {F : M → N} (p₀ q : M)
    (hq : q ∈ (chartAt H p₀).source)
    (hFq : F q ∈ (chartAt H' (F p₀)).source) :
    Function.Injective (mfderiv I J F q) ↔
      Function.Injective
        (inTangentCoordinates I J id F (mfderiv I J F) p₀ q) := by
  rw [inTangentCoordinates_eq_mfderiv_comp hq hFq]
  let B : TangentSpace J (F q) →L[ℝ] E' :=
    mfderiv J 𝓘(ℝ, E') (extChartAt J (F p₀)) (F q)
  let C : E →L[ℝ] TangentSpace I q :=
    mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I)
      (extChartAt I p₀ q)
  have hFqExt : F q ∈ (extChartAt J (F p₀)).source := by
    rwa [extChartAt_source]
  have hqExt : q ∈ (extChartAt I p₀).source := by
    rwa [extChartAt_source]
  have hB : B.IsInvertible := by
    simpa [B] using isInvertible_mfderiv_extChartAt hFqExt
  have hC : C.IsInvertible := by
    simpa [C] using
      isInvertible_mfderivWithin_extChartAt_symm
        ((extChartAt I p₀).map_source hqExt)
  calc
    Function.Injective (mfderiv I J F q) ↔
        Function.Injective (B.comp (mfderiv I J F q)) := by
          simpa [B] using!
            (Function.Injective.of_comp_iff hB.bijective.1
              (mfderiv I J F q)).symm
    _ ↔ Function.Injective ((B.comp (mfderiv I J F q)).comp C) := by
          simpa [C] using!
            (Function.Injective.of_comp_iff'
              (B.comp (mfderiv I J F q)) hC.bijective).symm

/-- Surjectivity of a manifold derivative is unchanged by the fixed chart-coordinate
identifications used by `inTangentCoordinates`. -/
private lemma surjective_mfderiv_iff_inTangentCoordinates
    {F : M → N} (p₀ q : M)
    (hq : q ∈ (chartAt H p₀).source)
    (hFq : F q ∈ (chartAt H' (F p₀)).source) :
    Function.Surjective (mfderiv I J F q) ↔
      Function.Surjective
        (inTangentCoordinates I J id F (mfderiv I J F) p₀ q) := by
  rw [inTangentCoordinates_eq_mfderiv_comp hq hFq]
  let B : TangentSpace J (F q) →L[ℝ] E' :=
    mfderiv J 𝓘(ℝ, E') (extChartAt J (F p₀)) (F q)
  let C : E →L[ℝ] TangentSpace I q :=
    mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I)
      (extChartAt I p₀ q)
  have hFqExt : F q ∈ (extChartAt J (F p₀)).source := by
    rwa [extChartAt_source]
  have hqExt : q ∈ (extChartAt I p₀).source := by
    rwa [extChartAt_source]
  have hB : B.IsInvertible := by
    simpa [B] using isInvertible_mfderiv_extChartAt hFqExt
  have hC : C.IsInvertible := by
    simpa [C] using
      isInvertible_mfderivWithin_extChartAt_symm
        ((extChartAt I p₀).map_source hqExt)
  calc
    Function.Surjective (mfderiv I J F q) ↔
        Function.Surjective (B.comp (mfderiv I J F q)) := by
          simpa [B] using!
            (Function.Surjective.of_comp_iff' hB.bijective
              (mfderiv I J F q)).symm
    _ ↔ Function.Surjective ((B.comp (mfderiv I J F q)).comp C) := by
          simpa [C] using!
            (Function.Surjective.of_comp_iff
              (B.comp (mfderiv I J F q)) hC.bijective.2).symm

/-- The injective-derivative locus of a smooth finite-dimensional manifold map is open. -/
private lemma isOpen_setOf_injective_mfderiv {F : M → N}
    (hF : ContMDiff I J ∞ F) :
    IsOpen {q : M | Function.Injective (mfderiv I J F q)} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  let A : M → E →L[ℝ] E' :=
    inTangentCoordinates I J id F (mfderiv I J F) p
  have hAcont : ContinuousAt A p := by
    have hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') 0 A p := by
      simpa [A] using
        hF.contMDiffAt.mfderiv_const (m := (0 : ℕ∞ω)) (by simp)
    exact hA.continuousAt
  have hpSource : p ∈ (chartAt H p).source := mem_chart_source H p
  have hpTarget : F p ∈ (chartAt H' (F p)).source := mem_chart_source H' (F p)
  have hAp : Function.Injective (A p) :=
    (injective_mfderiv_iff_inTangentCoordinates p p hpSource hpTarget).mp hp
  have hCharts :
      ({q : M | q ∈ (chartAt H p).source} ∩
          {q : M | F q ∈ (chartAt H' (F p)).source} ∩
            A ⁻¹' {L : E →L[ℝ] E' | Function.Injective L}) ∈ 𝓝 p := by
    refine Filter.inter_mem
      (Filter.inter_mem (chart_source_mem_nhds H p)
        (hF.continuous.continuousAt.preimage_mem_nhds
          (chart_source_mem_nhds H' (F p)))) ?_
    exact hAcont.preimage_mem_nhds
      (ContinuousLinearMap.isOpen_injective.mem_nhds hAp)
  refine Filter.mem_of_superset hCharts ?_
  intro q hq
  exact (injective_mfderiv_iff_inTangentCoordinates p q hq.1.1 hq.1.2).mpr hq.2

/-- The surjective-derivative locus of a smooth finite-dimensional manifold map is open. -/
private lemma isOpen_setOf_surjective_mfderiv {F : M → N}
    (hF : ContMDiff I J ∞ F) :
    IsOpen {q : M | Function.Surjective (mfderiv I J F q)} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  let A : M → E →L[ℝ] E' :=
    inTangentCoordinates I J id F (mfderiv I J F) p
  have hAcont : ContinuousAt A p := by
    have hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') 0 A p := by
      simpa [A] using
        hF.contMDiffAt.mfderiv_const (m := (0 : ℕ∞ω)) (by simp)
    exact hA.continuousAt
  have hpSource : p ∈ (chartAt H p).source := mem_chart_source H p
  have hpTarget : F p ∈ (chartAt H' (F p)).source := mem_chart_source H' (F p)
  have hAp : Function.Surjective (A p) :=
    (surjective_mfderiv_iff_inTangentCoordinates p p hpSource hpTarget).mp hp
  have hCharts :
      ({q : M | q ∈ (chartAt H p).source} ∩
          {q : M | F q ∈ (chartAt H' (F p)).source} ∩
            A ⁻¹' {L : E →L[ℝ] E' | Function.Surjective L}) ∈ 𝓝 p := by
    refine Filter.inter_mem
      (Filter.inter_mem (chart_source_mem_nhds H p)
        (hF.continuous.continuousAt.preimage_mem_nhds
          (chart_source_mem_nhds H' (F p)))) ?_
    exact hAcont.preimage_mem_nhds (isOpen_surjective_clm.mem_nhds hAp)
  refine Filter.mem_of_superset hCharts ?_
  intro q hq
  exact (surjective_mfderiv_iff_inTangentCoordinates p q hq.1.1 hq.1.2).mpr hq.2

/-- The differential of the inclusion of an open submanifold is surjective. -/
private lemma surjective_mfderiv_subtype_val (U : TopologicalSpace.Opens M) (x : U) :
    Function.Surjective (mfderiv I I (Subtype.val : U → M) x) := by
  classical
  let s : M → U := fun y ↦ if hy : y ∈ U then ⟨y, hy⟩ else x
  have hs_val : (Subtype.val ∘ s) =ᶠ[𝓝 (x : M)] id := by
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    change (s y : M) = y
    have hsy : s y = (⟨y, hy⟩ : U) := by
      dsimp [s]
      split
      · rfl
      · contradiction
    rw [hsy]
  have hs_smooth : ContMDiffAt I I ∞ s (x : M) := by
    apply (ContMDiffAt.subtypeVal_comp_iff U s (x : M)).mp
    exact contMDiffAt_id.congr_of_eventuallyEq hs_val
  have hval_smooth : MDifferentiableAt I I (Subtype.val : U → M) x :=
    (contMDiff_subtype_val (I := I) (U := U) (n := ∞)).contMDiffAt.mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hs_mdiff : MDifferentiableAt I I s (x : M) :=
    hs_smooth.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hsx : s (x : M) = x := by
    apply Subtype.ext
    have := hs_val.eq_of_nhds
    simpa using this
  have hval_smooth' : MDifferentiableAt I I (Subtype.val : U → M) (s (x : M)) := by
    simpa [hsx] using hval_smooth
  have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I)
    (f := s) (g := (Subtype.val : U → M)) (x := (x : M)) hval_smooth' hs_mdiff
  have hcomp_id :
      mfderiv I I ((Subtype.val : U → M) ∘ s) (x : M) =
        ContinuousLinearMap.id ℝ _ := by
    rw [hs_val.mfderiv_eq, mfderiv_id]
  have hright :
      (mfderiv I I (Subtype.val : U → M) x).comp
          (mfderiv I I s (x : M)) = ContinuousLinearMap.id ℝ _ := by
    rw [hsx] at hcomp
    exact hcomp.symm.trans hcomp_id
  exact (ContinuousLinearMap.rightInverse_of_comp hright).surjective

section InverseFunctionHelpers

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Invertible continuous linear maps form an open subset of the operator space. -/
private lemma isOpen_setOf_isInvertible_clm :
    IsOpen {A : X →L[ℝ] Y | A.IsInvertible} := by
  change IsOpen (Set.range (fun e : X ≃L[ℝ] Y ↦ (e : X →L[ℝ] Y)))
  exact ContinuousLinearEquiv.isOpen

/-- Shrink a smooth neighborhood until its derivative is invertible everywhere. -/
private lemma exists_open_with_invertible_fderiv
    {g : X → Y} {a : X} {Ω : Set X}
    (hΩ : Ω ∈ 𝓝 a) (hgΩ : ContDiffOn ℝ ∞ g Ω)
    (haInv : (fderiv ℝ g a).IsInvertible) :
    ∃ s : Set X, IsOpen s ∧ a ∈ s ∧ s ⊆ Ω ∧ ContDiffOn ℝ ∞ g s ∧
      ∀ x ∈ s, (fderiv ℝ g x).IsInvertible := by
  rcases mem_nhds_iff.mp hΩ with ⟨t, ht_subset, ht_open, ha_t⟩
  have hcont_t : ContinuousOn (fderiv ℝ g) t := by
    exact (hgΩ.mono ht_subset).continuousOn_fderiv_of_isOpen ht_open (by simp)
  have hpre_inv :
      (fderiv ℝ g) ⁻¹' {A : X →L[ℝ] Y | A.IsInvertible} ∈ 𝓝 a := by
    exact (hcont_t.continuousAt (ht_open.mem_nhds ha_t)).preimage_mem_nhds
      (isOpen_setOf_isInvertible_clm.mem_nhds haInv)
  rcases mem_nhds_iff.mp hpre_inv with ⟨u, hu_subset, hu_open, ha_u⟩
  refine ⟨t ∩ u, ht_open.inter hu_open, ⟨ha_t, ha_u⟩, ?_, ?_, ?_⟩
  · exact fun _ hx ↦ ht_subset hx.1
  · exact hgΩ.mono fun _ hx ↦ ht_subset hx.1
  · exact fun _ hx ↦ hu_subset hx.2

/-- On a restriction where the derivative stays invertible, the inverse-function-theorem
inverse branch is smooth on its entire target. -/
private lemma contDiffOn_symm_of_restricted_ift
    {g : X → Y} {a : X} {e : X ≃L[ℝ] Y}
    (hgAt : ContDiffAt ℝ ∞ g a)
    (hgDeriv : HasFDerivAt g (e : X →L[ℝ] Y) a)
    {s : Set X} (hs_open : IsOpen s)
    (hs_source : s ⊆ (hgAt.toOpenPartialHomeomorph g hgDeriv (by simp)).source)
    (hg_s : ContDiffOn ℝ ∞ g s)
    (hInv_s : ∀ x ∈ s, (fderiv ℝ g x).IsInvertible) :
    ContDiffOn ℝ ∞
      (hgAt.toOpenPartialHomeomorph g hgDeriv (by simp)).symm
      ((hgAt.toOpenPartialHomeomorph g hgDeriv (by simp)).restr s).target := by
  let R := hgAt.toOpenPartialHomeomorph g hgDeriv (by simp)
  have hsource_restr : (R.restr s).source = s := by
    rw [R.restr_source' s hs_open]
    exact Set.inter_eq_right.mpr hs_source
  rw [(R.restr s).open_target.contDiffOn_iff]
  intro y hy
  have hy' : y ∈ R.target ∧ R.symm y ∈ s := by
    simpa [OpenPartialHomeomorph.restr, hs_open.interior_eq, Set.mem_inter_iff,
      Set.mem_preimage] using hy
  let x : X := R.symm y
  have hx_cont : ContDiffAt ℝ ∞ g x :=
    (hg_s x hy'.2).contDiffAt (hs_open.mem_nhds hy'.2)
  have hx_deriv : HasFDerivAt g (fderiv ℝ g x) x :=
    (hx_cont.differentiableAt (by simp)).hasFDerivAt
  have hx_R_source : x ∈ R.source := hs_source hy'.2
  have hx_deriv' :
      HasFDerivAt g
        ((Classical.choose (hInv_s x hy'.2) : X ≃L[ℝ] Y) : X →L[ℝ] Y) x := by
    simpa [Classical.choose_spec (hInv_s x hy'.2)] using hx_deriv
  have hx_left : R.symm (g x) = x := by
    simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe] using R.left_inv hx_R_source
  have hx_derivR :
      HasFDerivAt R
        ((Classical.choose (hInv_s x hy'.2) : X ≃L[ℝ] Y) : X →L[ℝ] Y)
        (R.symm (g x)) := by
    simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, hx_left] using hx_deriv'
  have hx_contR : ContDiffAt ℝ ∞ R (R.symm (g x)) := by
    simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, hx_left] using hx_cont
  have hx_symm : ContDiffAt ℝ ∞ R.symm (g x) := by
    exact R.contDiffAt_symm (R.map_source hx_R_source) hx_derivR hx_contR
  have hy_eq : g (R.symm y) = y := by
    simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, x] using R.right_inv hy'.1
  simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, x, hy_eq] using hx_symm

/-- Package the ordinary inverse function theorem as a smooth partial diffeomorphism whose
source is contained in a prescribed smooth neighborhood. -/
private lemma partialDiffeomorph_of_ift
    {g : X → Y} {a : X} {Ω : Set X} {e : X ≃L[ℝ] Y}
    (hΩ : Ω ∈ 𝓝 a) (hgΩ : ContDiffOn ℝ ∞ g Ω)
    (hgAt : ContDiffAt ℝ ∞ g a)
    (hgDeriv : HasFDerivAt g (e : X →L[ℝ] Y) a)
    (haInv : (fderiv ℝ g a).IsInvertible) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, X) 𝓘(ℝ, Y) X Y ∞,
      a ∈ Ψ.source ∧ Ψ.source ⊆ Ω ∧ Set.EqOn g Ψ Ψ.source := by
  let R := hgAt.toOpenPartialHomeomorph g hgDeriv (by simp)
  have haR : a ∈ R.source := hgAt.mem_toOpenPartialHomeomorph_source hgDeriv (by simp)
  have hΩR : Ω ∩ R.source ∈ 𝓝 a :=
    Filter.inter_mem hΩ (R.open_source.mem_nhds haR)
  obtain ⟨s, hs_open, ha_s, hs_subset, hg_s, hInv_s⟩ :=
    exists_open_with_invertible_fderiv hΩR (hgΩ.mono Set.inter_subset_left) haInv
  have hs_Ω : s ⊆ Ω := fun _ hx ↦ (hs_subset hx).1
  have hs_R : s ⊆ R.source := fun _ hx ↦ (hs_subset hx).2
  have hsource_restr : (R.restr s).source = s := by
    rw [R.restr_source' s hs_open]
    exact Set.inter_eq_right.mpr hs_R
  have hsymm : ContDiffOn ℝ ∞ R.symm (R.restr s).target :=
    contDiffOn_symm_of_restricted_ift hgAt hgDeriv hs_open hs_R hg_s hInv_s
  let Ψ : PartialDiffeomorph 𝓘(ℝ, X) 𝓘(ℝ, Y) X Y ∞ :=
    { toPartialEquiv := (R.restr s).toPartialEquiv
      open_source := (R.restr s).open_source
      open_target := (R.restr s).open_target
      contMDiffOn_toFun := by
        rw [hsource_restr]
        simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe] using hg_s.contMDiffOn
      contMDiffOn_invFun := by
        simpa [R] using hsymm.contMDiffOn }
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · change a ∈ (R.restr s).source
    rwa [hsource_restr]
  · change (R.restr s).source ⊆ Ω
    rwa [hsource_restr]
  · intro x hx
    simpa [Ψ, R, ContDiffAt.toOpenPartialHomeomorph_coe]

end InverseFunctionHelpers

/-- A boundaryless model with corners is globally diffeomorphic to its model vector space. -/
private noncomputable def boundarylessModelDiffeomorph
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Type*} [TopologicalSpace K] (L : ModelWithCorners ℝ X K) [L.Boundaryless] :
    K ≃ₘ^∞⟮L, 𝓘(ℝ, X)⟯ X where
  toEquiv := L.toHomeomorph.toEquiv
  contMDiff_toFun := L.contMDiff
  contMDiff_invFun := by
    change ContMDiff (modelWithCornersSelf ℝ X) L ∞ L.symm
    rw [← contMDiffOn_univ]
    simpa [L.range_eq_univ] using (L.contMDiffOn_symm (n := ∞))

/-- Transition maps of restrictions of maximal-atlas charts remain smooth. -/
private lemma trans_subtypeRestr_mem_contDiffGroupoid
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    {U : TopologicalSpace.Opens M} (hU : Nonempty U) :
    (e.subtypeRestr hU).symm ≫ₕ e'.subtypeRestr hU ∈ contDiffGroupoid ∞ I :=
  (contDiffGroupoid ∞ I).mem_of_eqOnSource
    (closedUnderRestriction'
      ((contDiffGroupoid ∞ I).compatible_of_mem_maximalAtlas he he')
      (e.isOpen_inter_preimage_symm U.2))
    (e.subtypeRestr_symm_trans_subtypeRestr hU e')

/-- Restricting a maximal-atlas chart to an open subtype preserves maximal-atlas membership. -/
private lemma subtypeRestr_mem_maximalAtlas
    {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {U : TopologicalSpace.Opens M} (hU : Nonempty U) :
    e.subtypeRestr hU ∈ IsManifold.maximalAtlas I ∞ U := by
  intro e' he'
  obtain ⟨x, hx⟩ := TopologicalSpace.Opens.chart_eq hU he'
  rw [hx]
  exact ⟨trans_subtypeRestr_mem_contDiffGroupoid he
      (IsManifold.subset_maximalAtlas (chart_mem_atlas H (x : M))) hU,
    trans_subtypeRestr_mem_contDiffGroupoid
      (IsManifold.subset_maximalAtlas (chart_mem_atlas H (x : M))) he hU⟩

/-- A globally smooth manifold map is ordinarily smooth in its preferred extended charts on
the common chart domain. -/
private lemma writtenInExtChartAt_contDiffOn
    {F : M → N} {p : M} (hF : ContMDiff I J ∞ F) :
    ContDiffOn ℝ ∞ (writtenInExtChartAt I J p F : E → E')
      ((extChartAt I p).target ∩
        (F ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (F p)).source) := by
  let s : Set M := (extChartAt I p).source ∩ F ⁻¹' (extChartAt J (F p)).source
  have hs : s ⊆ (extChartAt I p).source := Set.inter_subset_left
  have hmaps : Set.MapsTo F s (extChartAt J (F p)).source := fun _ hx ↦ hx.2
  have hchart :
      ContDiffOn ℝ ∞ (writtenInExtChartAt I J p F : E → E')
        ((extChartAt I p) '' s) :=
    (contMDiffOn_iff_of_subset_source' (I := I) (I' := J) (n := ∞)
      (x := p) (y := F p) (f := F) hs hmaps).1 hF.contMDiffOn
  have himage :
      (extChartAt I p) '' s =
        ((extChartAt I p).target ∩
          (F ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (F p)).source) := by
    convert (extChartAt I p).image_source_inter_eq'
      (F ⁻¹' (extChartAt J (F p)).source) using 1 <;> ext x <;> rfl
  rwa [himage] at hchart

/-- Proposition 4.1 (1): if the manifold derivative of a smooth map is surjective at `p`, then
`p` has an open neighborhood on which the restricted map is a smooth submersion. -/
theorem exists_open_restriction_isSmoothSubmersion_of_surjective_mfderiv {F : M → N} {p : M}
    (hF : ContMDiff I J ∞ F) (hp : Function.Surjective (mfderiv I J F p)) :
    ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
      IsSmoothSubmersion I J (F ∘ (Subtype.val : U → M)) := by
  let U : TopologicalSpace.Opens M :=
    ⟨{q : M | Function.Surjective (mfderiv I J F q)},
      isOpen_setOf_surjective_mfderiv hF⟩
  refine ⟨U, hp, ?_⟩
  refine ⟨hF.comp contMDiff_subtype_val, ?_⟩
  intro x
  have hFsurj : Function.Surjective (mfderiv I J F (x : M)) := x.property
  have hvalsurj :
      Function.Surjective (mfderiv I I (Subtype.val : U → M) x) :=
    surjective_mfderiv_subtype_val U x
  have hFmd : MDifferentiableAt I J F (x : M) :=
    hF.contMDiffAt.mdifferentiableAt (by simp)
  have hvalmd : MDifferentiableAt I I (Subtype.val : U → M) x :=
    (contMDiff_subtype_val (I := I) (U := U) (n := ∞)).contMDiffAt.mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
  rw [mfderiv_comp x hFmd hvalmd]
  exact hFsurj.comp hvalsurj

private def preferredChartPartialDiffeomorph [I.Boundaryless] (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

/-- Proposition 4.1 (2): if the manifold derivative of a smooth map is injective at `p`, then
`p` has an open neighborhood on which the restricted map is a smooth immersion.
Both models are explicitly boundaryless, matching the ordinary-manifold statement.
The proof constructs a local chart from the inverse function theorem after adjoining a
linear complement to the derivative image. -/
theorem exists_open_restriction_isImmersion_of_injective_mfderiv {F : M → N} {p : M}
    [I.Boundaryless] [J.Boundaryless]
    (hF : ContMDiff I J ∞ F) (hp : Function.Injective (mfderiv I J F p)) :
    ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
      IsImmersion I J ∞ (F ∘ (Subtype.val : U → M)) := by
  let A : E →L[ℝ] E' := mfderiv I J F p
  have hleft : A.HasLeftInverse :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hp
  let G : Submodule ℝ E' := hleft.complement
  letI : CompleteSpace G := hleft.isClosed_complement.completeSpace_coe
  have hcompl : IsCompl A.range G := hleft.isCompl_complement
  have hker : A.ker = ⊥ := LinearMap.ker_eq_bot.2 hp
  let e : (E × G) ≃L[ℝ] E' := A.coprodSubtypeLEquivOfIsCompl hcompl hker
  let g : E → E' := writtenInExtChartAt I J p F
  let a : E := extChartAt I p p
  let γ : E × G → E' := fun z ↦ g z.1 + z.2.1
  let Ω0 : Set E := (extChartAt I p).target ∩
    (F ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (F p)).source
  let Ω : Set (E × G) := Ω0 ×ˢ (Set.univ : Set G)
  have hΩ0_target : (extChartAt I p).target ∈ nhds a := by
    simpa [a, I.range_eq_univ] using extChartAt_target_mem_nhdsWithin (I := I) p
  have hΩ0_source :
      (F ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (F p)).source ∈ nhds a := by
    convert extChartAt_preimage_mem_nhds (I := I) (x := p)
      (hF.continuous.continuousAt.preimage_mem_nhds
        (extChartAt_source_mem_nhds (I := J) (F p))) using 1 <;>
      ext x <;> rfl
  have hΩ0 : Ω0 ∈ nhds a := Filter.inter_mem hΩ0_target hΩ0_source
  have hΩ : Ω ∈ nhds (a, (0 : G)) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hΩ0 Filter.univ_mem
  have hgΩ0 : ContDiffOn ℝ ∞ g Ω0 := by
    simpa [g, Ω0] using writtenInExtChartAt_contDiffOn (I := I) (J := J) hF
  have hγΩ : ContDiffOn ℝ ∞ γ Ω := by
    exact (hgΩ0.comp contDiffOn_fst (fun z hz ↦ hz.1)).add
      (G.subtypeL.contDiff.comp contDiff_snd).contDiffOn
  have hmd : MDifferentiableAt I J F p :=
    hF.contMDiffAt.mdifferentiableAt (by simp)
  have hgDeriv : HasFDerivAt g A a := by
    simpa [g, A, a, I.range_eq_univ] using hmd.hasMFDerivAt.2
  have hγDeriv : HasFDerivAt γ (e : (E × G) →L[ℝ] E') (a, (0 : G)) := by
    have hd := (hgDeriv.comp (a, (0 : G)) hasFDerivAt_fst).add
      (G.subtypeL.hasFDerivAt.comp (a, (0 : G)) hasFDerivAt_snd)
    convert hd using 1 <;> first | rfl | (ext z; rfl)
  have hγAt : ContDiffAt ℝ ∞ γ (a, (0 : G)) := hγΩ.contDiffAt hΩ
  have haInv : (fderiv ℝ γ (a, (0 : G))).IsInvertible := by
    rw [hγDeriv.fderiv]
    exact ⟨e, rfl⟩
  obtain ⟨Ψ, hbase, hΨsub, hΨeq⟩ :=
    partialDiffeomorph_of_ift hΩ hγΩ hγAt hγDeriv haInv
  let C := preferredChartPartialDiffeomorph (I := J) (F p)
  let P : PartialDiffeomorph J J N H' ∞ :=
    ((C.trans Ψ.symm).trans e.toDiffeomorph.toPartialDiffeomorph).trans
      (boundarylessModelDiffeomorph J).symm.toPartialDiffeomorph
  let codChart : OpenPartialHomeomorph N H' := P.toOpenPartialHomeomorph
  have hγbase : γ (a, (0 : G)) = extChartAt J (F p) (F p) := by
    change extChartAt J (F p) (F ((extChartAt I p).symm (extChartAt I p p))) + 0 = _
    rw [add_zero, (extChartAt I p).left_inv (mem_extChartAt_source p)]
  have hcodp : F p ∈ codChart.source := by
    change ((F p ∈ (extChartAt J (F p)).source ∧
      extChartAt J (F p) (F p) ∈ Ψ.target) ∧ _ ∈ Set.univ) ∧ _ ∈ Set.univ
    refine ⟨⟨⟨mem_extChartAt_source (F p), ?_⟩, Set.mem_univ _⟩, Set.mem_univ _⟩
    have hm := Ψ.map_source hbase
    rw [← hΨeq hbase, hγbase] at hm
    exact hm
  have hcod : codChart ∈ IsManifold.maximalAtlas J ∞ N :=
    codChart.mem_maximalAtlas_of_contMDiffOn P.contMDiffOn_toFun P.contMDiffOn_invFun
  let D := preferredChartPartialDiffeomorph (I := I) p
  let U : Set M := (extChartAt I p).source ∩
    (fun x : M ↦ (extChartAt I p x, (0 : G))) ⁻¹' Ψ.source
  have hU : IsOpen U :=
    (D.contMDiffOn_toFun.continuousOn.prodMk continuousOn_const).isOpen_inter_preimage
      D.open_source Ψ.open_source
  let domChart := (chartAt H p).restrOpen U hU
  have hdomp : p ∈ domChart.source :=
    ⟨mem_chart_source H p, mem_extChartAt_source p, hbase⟩
  have hdom : domChart ∈ IsManifold.maximalAtlas I ∞ M :=
    domChart.mem_maximalAtlas_of_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)).mono
        Set.inter_subset_left)
      ((contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)).mono
        Set.inter_subset_left)
  have hwritten : Set.EqOn ((codChart.extend J) ∘ F ∘ (domChart.extend I).symm)
      (e ∘ fun x : E ↦ (x, (0 : G))) (domChart.extend I).target := by
    intro y hy
    let x : M := (domChart.extend I).symm y
    have hxdom : x ∈ domChart.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using (domChart.extend I).map_target hy
    have hxU : (extChartAt I p x, (0 : G)) ∈ Ψ.source := hxdom.2.2
    have hdomcoord : extChartAt I p x = y := (domChart.extend I).right_inv hy
    have hxγ : γ (extChartAt I p x, (0 : G)) = extChartAt J (F p) (F x) := by
      change extChartAt J (F p) (F ((extChartAt I p).symm (extChartAt I p x))) + 0 = _
      rw [add_zero, (extChartAt I p).left_inv hxdom.2.1]
    have hinv : Ψ.symm (extChartAt J (F p) (F x)) = (y, (0 : G)) := by
      rw [← hxγ, hΨeq hxU]
      exact (Ψ.left_inv hxU).trans (congrArg (fun z : E ↦ (z, (0 : G))) hdomcoord)
    change J (J.symm (e (Ψ.symm (extChartAt J (F p) (F x))))) = e (y, 0)
    rw [J.right_inv (by rw [J.range_eq_univ]; exact Set.mem_univ _), hinv]
  let hpImm := (IsImmersionAtOfComplement.mk_of_continuousAt
    (I := I) (J := J) (n := ∞) hF.continuous.continuousAt e
    domChart codChart hdomp hcodp hdom hcod hwritten).isImmersionAt
  exact ⟨⟨hpImm.domChart.source, hpImm.domChart.open_source⟩,
    hpImm.mem_domChart_source, isImmersion_restrict_domChart hpImm⟩

end

end Manifold
