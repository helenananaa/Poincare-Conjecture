import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_1
import LeeSmoothLib.Ch04.Sec04_21.Proposition_4_1.Core
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1

open scoped ContDiff Manifold Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Manifold

open Set Function

private lemma halfSpace_local_ambient_extension
    {n : ℕ} [NeZero n]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set (EuclideanHalfSpace n)}
    {f : EuclideanHalfSpace n → F}
    (hU : IsOpen U)
    (hCont : ContDiffOn ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
      ((𝓡∂ n) '' U))
    {x : EuclideanHalfSpace n} (hx : x ∈ U) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x.1 ∈ V ∧ ((𝓡∂ n) ⁻¹' V) ⊆ U ∧
      ∃ g : EuclideanSpace ℝ (Fin n) → F,
        ContDiffOn ℝ ∞ g V ∧
          Set.EqOn g (fun z ↦ f ((𝓡∂ n).symm z))
            (V ∩ Set.range (𝓡∂ n)) := by
  rcases open_halfSpace_neighborhood_of_open_subtype_set (U := U) hU hx with
    ⟨W, hW, hxW, hWU⟩
  rcases lt_or_eq_of_le x.2 with hxpos | hxzero
  · refine ⟨W ∩ interior (Set.range (𝓡∂ n)), hW.inter isOpen_interior, ?_, ?_, ?_⟩
    · have hxInterior : x.1 ∈ interior (Set.range (𝓡∂ n)) := by
        rw [interior_range_modelWithCornersEuclideanHalfSpace n]
        exact hxpos
      exact ⟨hxW, hxInterior⟩
    · intro y hy
      exact hWU hy.1
    · refine ⟨fun z ↦ f ((𝓡∂ n).symm z), ?_, ?_⟩
      · apply hCont.mono
        intro y hy
        apply ambient_range_slice_subset_halfSpace_image (U := U) hWU
        exact ⟨hy.1, interior_subset hy.2⟩
      · intro y hy
        rfl
  · have hxzero' : x.1 0 = 0 := hxzero.symm
    have hRange : Set.range (𝓡∂ n) =
        LeeSmooth.SeeleyExtension.closedUpperHalfSpace (n := n) := by
      simpa [LeeSmooth.SeeleyExtension.closedUpperHalfSpace] using
        range_modelWithCornersEuclideanHalfSpace n
    have hContW : ContDiffOn ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
        (W ∩ LeeSmooth.SeeleyExtension.closedUpperHalfSpace (n := n)) := by
      rw [← hRange]
      apply hCont.mono
      intro y hy
      exact ambient_range_slice_subset_halfSpace_image (U := U) hWU hy
    obtain ⟨V, hV, hxV, hVW, g, hg, hEq⟩ :=
      LeeSmooth.SeeleyExtension.contDiffOn_closedUpperHalfSpace_exists_open_extension_at
        hW hxW hxzero' hContW
    have hEqRange : Set.EqOn g (fun z ↦ f ((𝓡∂ n).symm z))
        (V ∩ Set.range (𝓡∂ n)) := by
      simpa [hRange] using hEq
    refine ⟨V, hV, hxV, ?_, g, hg, hEqRange⟩
    intro y hy
    exact hWU (hVW hy)

section InverseFunctionHelpers

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private lemma halfSpace_isOpen_setOf_isInvertible_clm :
    IsOpen {A : X →L[ℝ] Y | A.IsInvertible} := by
  change IsOpen (Set.range (fun e : X ≃L[ℝ] Y ↦ (e : X →L[ℝ] Y)))
  exact ContinuousLinearEquiv.isOpen

private lemma halfSpace_exists_open_with_invertible_fderiv
    {g : X → Y} {a : X} {Ω : Set X}
    (hΩ : Ω ∈ 𝓝 a) (hgΩ : ContDiffOn ℝ ∞ g Ω)
    (haInv : (fderiv ℝ g a).IsInvertible) :
    ∃ s : Set X, IsOpen s ∧ a ∈ s ∧ s ⊆ Ω ∧ ContDiffOn ℝ ∞ g s ∧
      ∀ x ∈ s, (fderiv ℝ g x).IsInvertible := by
  rcases mem_nhds_iff.mp hΩ with ⟨t, ht_subset, ht_open, ha_t⟩
  have hcont_t : ContinuousOn (fderiv ℝ g) t :=
    (hgΩ.mono ht_subset).continuousOn_fderiv_of_isOpen ht_open (by simp)
  have hpre_inv :
      (fderiv ℝ g) ⁻¹' {A : X →L[ℝ] Y | A.IsInvertible} ∈ 𝓝 a :=
    (hcont_t.continuousAt (ht_open.mem_nhds ha_t)).preimage_mem_nhds
      (halfSpace_isOpen_setOf_isInvertible_clm.mem_nhds haInv)
  rcases mem_nhds_iff.mp hpre_inv with ⟨u, hu_subset, hu_open, ha_u⟩
  refine ⟨t ∩ u, ht_open.inter hu_open, ⟨ha_t, ha_u⟩, ?_, ?_, ?_⟩
  · exact fun _ hx ↦ ht_subset hx.1
  · exact hgΩ.mono fun _ hx ↦ ht_subset hx.1
  · exact fun _ hx ↦ hu_subset hx.2

private lemma halfSpace_contDiffOn_symm_of_restricted_ift
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
    simpa [OpenPartialHomeomorph.restr, hs_open.interior_eq,
      Set.mem_inter_iff, Set.mem_preimage] using hy
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

private lemma halfSpace_partialDiffeomorph_of_ift
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
    halfSpace_exists_open_with_invertible_fderiv hΩR
      (hgΩ.mono Set.inter_subset_left) haInv
  have hs_Ω : s ⊆ Ω := fun _ hx ↦ (hs_subset hx).1
  have hs_R : s ⊆ R.source := fun _ hx ↦ (hs_subset hx).2
  have hsource_restr : (R.restr s).source = s := by
    rw [R.restr_source' s hs_open]
    exact Set.inter_eq_right.mpr hs_R
  have hsymm : ContDiffOn ℝ ∞ R.symm (R.restr s).target :=
    halfSpace_contDiffOn_symm_of_restricted_ift hgAt hgDeriv hs_open hs_R hg_s hInv_s
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

private noncomputable def halfSpace_boundarylessModelDiffeomorph
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Type*} [TopologicalSpace K] (L : ModelWithCorners ℝ X K) [L.Boundaryless] :
    K ≃ₘ^∞⟮L, 𝓘(ℝ, X)⟯ X where
  toEquiv := L.toHomeomorph.toEquiv
  contMDiff_toFun := L.contMDiff
  contMDiff_invFun := by
    change ContMDiff (modelWithCornersSelf ℝ X) L ∞ L.symm
    rw [← contMDiffOn_univ]
    simpa [L.range_eq_univ] using (L.contMDiffOn_symm (n := ∞))

private noncomputable def halfSpace_continuousLinearEquivDiffeomorph
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : X ≃L[ℝ] Y) :
    Diffeomorph 𝓘(ℝ, X) 𝓘(ℝ, Y) X Y ∞ where
  toEquiv := e.toLinearEquiv.toEquiv
  contMDiff_toFun := e.contDiff.contMDiff
  contMDiff_invFun := e.symm.contDiff.contMDiff

private def halfSpace_preferredChartPartialDiffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa [extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

universe uE' uH' uM uN

variable {n : ℕ} [NeZero n]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N]

/-- Pointwise half-space immersion criterion.  The source chart is the original half-space chart;
the ambient map used by the inverse function theorem is only an extension of its representative. -/
theorem isImmersionAt_of_injective_mfderiv_halfSpace
    {F : M → N} {p : M}
    (hF : ContMDiff (𝓡∂ n) J ∞ F)
    (hp : Function.Injective (mfderiv (𝓡∂ n) J F p)) :
    IsImmersionAt (𝓡∂ n) J ∞ F p := by
  let I := 𝓡∂ n
  let dom0 := chartAt (EuclideanHalfSpace n) p
  let cod0 := chartAt H' (F p)
  let s : Set M := dom0.source ∩ F ⁻¹' cod0.source
  let U0 : Set (EuclideanHalfSpace n) :=
    dom0.target ∩ dom0.symm ⁻¹' (F ⁻¹' cod0.source)
  let f0 : EuclideanHalfSpace n → E' := cod0.extend J ∘ F ∘ dom0.symm
  let g : EuclideanSpace ℝ (Fin n) → E' :=
    writtenInExtChartAt (𝓡∂ n) J p F
  let a : EuclideanSpace ℝ (Fin n) := I (dom0 p)
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] E' :=
    mfderiv (𝓡∂ n) J F p
  have hU0 : IsOpen U0 := by
    apply dom0.isOpen_inter_preimage_symm
    exact hF.continuous.isOpen_preimage _ cod0.open_source
  have hs : s ⊆ dom0.source := inter_subset_left
  have hmaps : MapsTo F s cod0.source := fun _ hx ↦ hx.2
  have himage : (dom0.extend I) '' s = I '' U0 := by
    simp only [s, U0, OpenPartialHomeomorph.extend_coe, Function.comp_def]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨dom0 x, ?_, rfl⟩
      refine ⟨dom0.map_source hx.1, ?_⟩
      simpa [dom0.left_inv hx.1] using hx.2
    · rintro ⟨u, hu, rfl⟩
      refine ⟨dom0.symm u, ?_, ?_⟩
      · exact ⟨dom0.map_target hu.1, hu.2⟩
      · simp [dom0.right_inv hu.1]
  have hg_s : ContDiffOn ℝ ∞ g ((dom0.extend I) '' s) := by
    have h :=
      (dom0.contMDiffOn_writtenInExtend_iff
        (I := I) (J := J)
        (IsManifold.chart_mem_maximalAtlas p)
        (IsManifold.chart_mem_maximalAtlas (F p))
        hs hmaps).2 (hF.contMDiffOn.mono (subset_univ s))
    rw [contMDiffOn_iff_contDiffOn] at h
    simpa [g, f0, writtenInExtChartAt, dom0, cod0,
      OpenPartialHomeomorph.extend_coe_symm, Function.comp_assoc] using h
  have hg_U0 : ContDiffOn ℝ ∞ g (I '' U0) := by
    rw [← himage]
    exact hg_s
  have hpU0 : dom0 p ∈ U0 := by
    refine ⟨dom0.map_source (mem_chart_source (EuclideanHalfSpace n) p), ?_⟩
    change F (dom0.symm (dom0 p)) ∈ cod0.source
    rw [dom0.left_inv (mem_chart_source (EuclideanHalfSpace n) p)]
    exact mem_chart_source H' (F p)
  obtain ⟨V, hV, haV, hVpre, gExt, hgExt, hEq⟩ :=
    halfSpace_local_ambient_extension (n := n) (U := U0) (f := f0)
      hU0 hg_U0 hpU0
  have haV' : a ∈ V := by
    simpa [a, I, modelWithCornersEuclideanHalfSpace] using haV
  have haRange : a ∈ Set.range I := by
    exact ⟨dom0 p, by rfl⟩
  have hEqAt : gExt a = g a := by
    have h := hEq ⟨(by simpa [I, modelWithCornersEuclideanHalfSpace] using haV),
      ⟨dom0 p, rfl⟩⟩
    simpa [a, I, g, writtenInExtChartAt, f0, cod0, dom0, extChartAt,
      modelWithCornersEuclideanHalfSpace] using h
  have hmd : MDifferentiableAt I J F p :=
    hF.contMDiffAt.mdifferentiableAt (by simp)
  have hderivG : HasFDerivWithinAt g A (Set.range I) a := by
    simpa [g, A, a, I] using hmd.hasMFDerivAt.2
  have hderivExtWithin : HasFDerivWithinAt gExt A (Set.range I) a := by
    apply hderivG.congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds haV'),
        self_mem_nhdsWithin] with y hyV hyRange
      exact hEq ⟨hyV, hyRange⟩
    · exact hEqAt
  have hderivExt : HasFDerivAt gExt A a := by
    have hdiff : DifferentiableAt ℝ gExt a :=
      (hgExt.contDiffAt (hV.mem_nhds haV')).differentiableAt (by simp)
    have hfd : fderiv ℝ gExt a = A := by
      rw [← fderivWithin_eq_fderiv (I.uniqueDiffWithinAt_image) hdiff]
      exact hderivExtWithin.fderivWithin (I.uniqueDiffWithinAt_image)
    rw [← hfd]
    exact hdiff.hasFDerivAt
  have hleft : A.HasLeftInverse :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hp
  let G : Submodule ℝ E' := hleft.complement
  letI : CompleteSpace G := hleft.isClosed_complement.completeSpace_coe
  have hcompl : IsCompl A.range G := hleft.isCompl_complement
  have hker : A.ker = ⊥ := LinearMap.ker_eq_bot.2 hp
  let e : (EuclideanSpace ℝ (Fin n) × G) ≃L[ℝ] E' :=
    A.coprodSubtypeLEquivOfIsCompl hcompl hker
  let γ : EuclideanSpace ℝ (Fin n) × G → E' :=
    fun z ↦ gExt z.1 + z.2.1
  let Ω : Set (EuclideanSpace ℝ (Fin n) × G) := V ×ˢ (Set.univ : Set G)
  have hΩ : Ω ∈ 𝓝 (a, (0 : G)) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hV.mem_nhds haV') Filter.univ_mem
  have hγΩ : ContDiffOn ℝ ∞ γ Ω := by
    exact (hgExt.comp contDiffOn_fst (fun z hz ↦ hz.1)).add
      (G.subtypeL.contDiff.comp contDiff_snd).contDiffOn
  have hγDeriv :
      HasFDerivAt γ (e : (EuclideanSpace ℝ (Fin n) × G) →L[ℝ] E')
        (a, (0 : G)) := by
    have hd := (hderivExt.comp (a, (0 : G)) hasFDerivAt_fst).add
      (G.subtypeL.hasFDerivAt.comp (a, (0 : G)) hasFDerivAt_snd)
    convert hd using 1 <;> first | rfl | (ext z; rfl)
  have hγAt : ContDiffAt ℝ ∞ γ (a, (0 : G)) := hγΩ.contDiffAt hΩ
  have haInv : (fderiv ℝ γ (a, (0 : G))).IsInvertible := by
    rw [hγDeriv.fderiv]
    exact ⟨e, rfl⟩
  obtain ⟨Ψ, hbase, hΨsub, hΨeq⟩ :=
    halfSpace_partialDiffeomorph_of_ift hΩ hγΩ hγAt hγDeriv haInv
  let C := halfSpace_preferredChartPartialDiffeomorph (I := J) (F p)
  let P : PartialDiffeomorph J J N H' ∞ :=
    ((C.trans Ψ.symm).trans
      (halfSpace_continuousLinearEquivDiffeomorph e).toPartialDiffeomorph).trans
      (halfSpace_boundarylessModelDiffeomorph J).symm.toPartialDiffeomorph
  let codChart : OpenPartialHomeomorph N H' := P.toOpenPartialHomeomorph
  have hγbase : γ (a, (0 : G)) = extChartAt J (F p) (F p) := by
    change gExt a + 0 = _
    rw [hEqAt, add_zero]
    change (cod0.extend J) (F (dom0.symm (I.symm a))) =
      extChartAt J (F p) (F p)
    have haI : I.symm a = dom0 p := by
      change I.symm (I (dom0 p)) = dom0 p
      apply I.left_inv
    rw [haI, dom0.left_inv (mem_chart_source (EuclideanHalfSpace n) p)]
    rfl
  have hcodp : F p ∈ codChart.source := by
    change ((F p ∈ (extChartAt J (F p)).source ∧
      extChartAt J (F p) (F p) ∈ Ψ.target) ∧ _ ∈ Set.univ) ∧ _ ∈ Set.univ
    refine ⟨⟨⟨mem_extChartAt_source (F p), ?_⟩, Set.mem_univ _⟩,
      Set.mem_univ _⟩
    have hm := Ψ.map_source hbase
    rw [← hΨeq hbase, hγbase] at hm
    exact hm
  have hcod : codChart ∈ IsManifold.maximalAtlas J ∞ N :=
    codChart.mem_maximalAtlas_of_contMDiffOn
      P.contMDiffOn_toFun P.contMDiffOn_invFun
  let U : Set M := (extChartAt I p).source ∩
    (fun x : M ↦ (extChartAt I p x, (0 : G))) ⁻¹' Ψ.source
  have hU : IsOpen U := by
    change IsOpen ((extChartAt I p).source ∩
      (fun x : M ↦ (extChartAt I p x, (0 : G))) ⁻¹' Ψ.source)
    exact (continuousOn_extChartAt p).prodMk continuousOn_const |>.isOpen_inter_preimage
      (isOpen_extChartAt_source p) Ψ.open_source
  let domChart := dom0.restrOpen U hU
  have hdomp : p ∈ domChart.source := by
    refine ⟨mem_chart_source (EuclideanHalfSpace n) p,
      mem_extChartAt_source p, ?_⟩
    simpa [a, I, extChartAt, dom0] using hbase
  have hdom : domChart ∈ IsManifold.maximalAtlas I ∞ M :=
    domChart.mem_maximalAtlas_of_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)).mono
        Set.inter_subset_left)
      ((contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)).mono
        Set.inter_subset_left)
  have hwritten : Set.EqOn ((codChart.extend J) ∘ F ∘ (domChart.extend I).symm)
      (e ∘ fun x : EuclideanSpace ℝ (Fin n) ↦ (x, (0 : G)))
      (domChart.extend I).target := by
    intro y hy
    let x : M := (domChart.extend I).symm y
    have hxdom : x ∈ domChart.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using
        (domChart.extend I).map_target hy
    have hxU : (extChartAt I p x, (0 : G)) ∈ Ψ.source := hxdom.2.2
    have hdomcoord : extChartAt I p x = y := by
      exact (domChart.extend I).right_inv hy
    have hxγ : γ (extChartAt I p x, (0 : G)) = extChartAt J (F p) (F x) := by
      change gExt (extChartAt I p x) + 0 = _
      rw [add_zero, hEq]
      · change f0 (I.symm (extChartAt I p x)) = extChartAt J (F p) (F x)
        have hxI : I.symm (extChartAt I p x) = dom0 x := by
          change I.symm (I (dom0 x)) = dom0 x
          apply I.left_inv
        rw [hxI]
        change (cod0.extend J) (F (dom0.symm (dom0 x))) =
          extChartAt J (F p) (F x)
        rw [dom0.left_inv hxdom.1]
        rfl
      · exact ⟨(hΨsub hxU).1, ⟨dom0 x, rfl⟩⟩
    have hinv : Ψ.symm (extChartAt J (F p) (F x)) = (y, (0 : G)) := by
      rw [← hxγ, hΨeq hxU]
      exact (Ψ.left_inv hxU).trans
        (congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ (z, (0 : G))) hdomcoord)
    change J (J.symm (e (Ψ.symm (extChartAt J (F p) (F x))))) = e (y, 0)
    rw [J.right_inv (by rw [J.range_eq_univ]; exact Set.mem_univ _), hinv]
  exact (IsImmersionAtOfComplement.mk_of_continuousAt
    (I := I) (J := J) (n := ∞) hF.continuous.continuousAt e
    domChart codChart hdomp hcodp hdom hcod hwritten).isImmersionAt

private lemma halfSpace_finiteDimensional_complement
    {F : M → N} {p : M}
    (h : IsImmersionAt (𝓡∂ n) J ∞ F p) :
    FiniteDimensional ℝ h.complement := by
  let e := h.isImmersionAtOfComplement_complement.equiv
  haveI : FiniteDimensional ℝ
      (EuclideanSpace ℝ (Fin n) × h.complement) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  exact FiniteDimensional.of_injective
    (LinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) h.complement)
    LinearMap.inr_injective

private lemma halfSpace_finrank_prod_complement
    {F : M → N} {p : M}
    (h : IsImmersionAt (𝓡∂ n) J ∞ F p) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) +
        Module.finrank ℝ h.complement = Module.finrank ℝ E' := by
  let e := h.isImmersionAtOfComplement_complement.equiv
  letI : FiniteDimensional ℝ h.complement :=
    halfSpace_finiteDimensional_complement h
  have hsum : Module.finrank ℝ
      (EuclideanSpace ℝ (Fin n) × h.complement) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) +
        Module.finrank ℝ h.complement := Module.finrank_prod
  have heq : Module.finrank ℝ
      (EuclideanSpace ℝ (Fin n) × h.complement) = Module.finrank ℝ E' :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  exact hsum.symm.trans heq

/-- Global half-space immersion criterion.  A single complement is fixed from one base point;
the finite-dimensional coordinate equivalence transports every other pointwise complement to it. -/
theorem isImmersion_of_injective_mfderiv_halfSpace
    {F : M → N}
    (hF : ContMDiff (𝓡∂ n) J ∞ F)
    (h : ∀ p : M, Function.Injective (mfderiv (𝓡∂ n) J F p)) :
    IsImmersion (𝓡∂ n) J ∞ F := by
  classical
  by_cases hEmpty : IsEmpty M
  · exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ (IsEmpty.false x).elim⟩
  obtain ⟨p0⟩ := not_isEmpty_iff.mp hEmpty
  let h0 := isImmersionAt_of_injective_mfderiv_halfSpace hF (h p0)
  let G0 := h0.complement
  refine ⟨G0, inferInstance, inferInstance, ?_⟩
  intro p
  let hp := isImmersionAt_of_injective_mfderiv_halfSpace hF (h p)
  letI : FiniteDimensional ℝ hp.complement :=
    halfSpace_finiteDimensional_complement hp
  letI : FiniteDimensional ℝ G0 :=
    halfSpace_finiteDimensional_complement h0
  have hEq : Module.finrank ℝ hp.complement = Module.finrank ℝ G0 :=
    Nat.add_left_cancel
      ((halfSpace_finrank_prod_complement hp).trans
        (halfSpace_finrank_prod_complement h0).symm)
  let eG : hp.complement ≃L[ℝ] G0 :=
    ContinuousLinearEquiv.ofFinrankEq hEq
  exact hp.isImmersionAtOfComplement_complement.trans_F eG

/-- In dimension zero the source is the existing boundaryless self-model `𝓡 0`; this wrapper
uses the established global self-model characterization instead of introducing a half-space
model with a nonexistent `NeZero 0` instance. -/
theorem isImmersion_of_injective_mfderiv_zero_selfModel
    {H₀ : Type uH'} [TopologicalSpace H₀]
    {J₀ : ModelWithCorners ℝ E' H₀} [J₀.Boundaryless]
    {M₀ : Type uM} [TopologicalSpace M₀]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M₀]
    [IsManifold (𝓡 0) ∞ M₀]
    {N₀ : Type uN} [TopologicalSpace N₀] [ChartedSpace H₀ N₀]
    [IsManifold J₀ ∞ N₀]
    {F₀ : M₀ → N₀}
    (hF₀ : ContMDiff (𝓡 0) J₀ ∞ F₀)
    (h₀ : ∀ p : M₀,
      Function.Injective (mfderiv (𝓡 0) J₀ F₀ p)) :
    IsImmersion (𝓡 0) J₀ ∞ F₀ :=
  (is_immersion_iff_forall_injective_mfderiv hF₀).2 h₀

end Manifold
