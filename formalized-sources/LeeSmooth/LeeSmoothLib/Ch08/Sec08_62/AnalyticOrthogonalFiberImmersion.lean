import Mathlib.Geometry.Manifold.LocalDiffeomorph
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5

/-!
Analytic immersion criterion from injective `mfderiv`, copied from Example 5.9's
checked inverse-function packing and specialized only by namespace.
-/

open scoped Manifold ContDiff

noncomputable section

namespace AnalyticOrthogonalFiberImmersion

open Manifold Topology

universe uE uE' uH uH' uM uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

section InverseFunctionHelpers

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Invertible continuous linear maps form an open subset of the operator space. -/
private lemma isOpen_setOf_isInvertible_clm :
    IsOpen {A : X →L[ℝ] Y | A.IsInvertible} := by
  change IsOpen (Set.range (fun e : X ≃L[ℝ] Y ↦ (e : X →L[ℝ] Y)))
  exact ContinuousLinearEquiv.isOpen

/-- Shrink an analytic neighborhood until its derivative is invertible everywhere. -/
private lemma exists_open_with_invertible_fderiv
    {g : X → Y} {a : X} {Ω : Set X}
    (hΩ : Ω ∈ 𝓝 a) (hgΩ : ContDiffOn ℝ (⊤ : ℕ∞ω) g Ω)
    (haInv : (fderiv ℝ g a).IsInvertible) :
    ∃ s : Set X, IsOpen s ∧ a ∈ s ∧ s ⊆ Ω ∧
      ContDiffOn ℝ (⊤ : ℕ∞ω) g s ∧
      ∀ x ∈ s, (fderiv ℝ g x).IsInvertible := by
  rcases mem_nhds_iff.mp hΩ with ⟨t, ht_subset, ht_open, ha_t⟩
  have hgΩ_infty : ContDiffOn ℝ (∞ : ℕ∞ω) g Ω := hgΩ.of_le (by simp)
  have hcont_t : ContinuousOn (fderiv ℝ g) t := by
    exact (hgΩ_infty.mono ht_subset).continuousOn_fderiv_of_isOpen ht_open (by simp)
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
inverse branch is analytic on its entire target. -/
private lemma contDiffOn_symm_of_restricted_ift
    {g : X → Y} {a : X} {e : X ≃L[ℝ] Y}
    (hgAt : ContDiffAt ℝ (⊤ : ℕ∞ω) g a)
    (hgDeriv : HasFDerivAt g (e : X →L[ℝ] Y) a)
    {s : Set X} (hs_open : IsOpen s)
    (hs_source : s ⊆ (hgAt.toOpenPartialHomeomorph g hgDeriv (by simp)).source)
    (hg_s : ContDiffOn ℝ (⊤ : ℕ∞ω) g s)
    (hInv_s : ∀ x ∈ s, (fderiv ℝ g x).IsInvertible) :
    ContDiffOn ℝ (⊤ : ℕ∞ω)
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
  have hx_cont : ContDiffAt ℝ (⊤ : ℕ∞ω) g x :=
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
  have hx_contR : ContDiffAt ℝ (⊤ : ℕ∞ω) R (R.symm (g x)) := by
    simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, hx_left] using hx_cont
  have hx_symm : ContDiffAt ℝ (⊤ : ℕ∞ω) R.symm (g x) := by
    exact R.contDiffAt_symm (R.map_source hx_R_source) hx_derivR hx_contR
  have hy_eq : g (R.symm y) = y := by
    simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, x] using R.right_inv hy'.1
  simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, x, hy_eq] using hx_symm

/-- The inverse function theorem packaged as an analytic partial diffeomorphism. -/
private lemma partialDiffeomorph_of_ift
    {g : X → Y} {a : X} {Ω : Set X} {e : X ≃L[ℝ] Y}
    (hΩ : Ω ∈ 𝓝 a) (hgΩ : ContDiffOn ℝ (⊤ : ℕ∞ω) g Ω)
    (hgAt : ContDiffAt ℝ (⊤ : ℕ∞ω) g a)
    (hgDeriv : HasFDerivAt g (e : X →L[ℝ] Y) a)
    (haInv : (fderiv ℝ g a).IsInvertible) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, X) 𝓘(ℝ, Y) X Y (⊤ : ℕ∞ω),
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
  have hsymm : ContDiffOn ℝ (⊤ : ℕ∞ω) R.symm (R.restr s).target :=
    contDiffOn_symm_of_restricted_ift hgAt hgDeriv hs_open hs_R hg_s hInv_s
  let Ψ : PartialDiffeomorph 𝓘(ℝ, X) 𝓘(ℝ, Y) X Y (⊤ : ℕ∞ω) :=
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

/-- A boundaryless analytic model with corners is analytically diffeomorphic to its model space. -/
private noncomputable def boundarylessModelDiffeomorph
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Type*} [TopologicalSpace K] (L : ModelWithCorners ℝ X K) [L.Boundaryless] :
    Diffeomorph L 𝓘(ℝ, X) K X (⊤ : ℕ∞ω) where
  toEquiv := L.toHomeomorph.toEquiv
  contMDiff_toFun := L.contMDiff
  contMDiff_invFun := by
    change ContMDiff (modelWithCornersSelf ℝ X) L (⊤ : ℕ∞ω) L.symm
    rw [← contMDiffOn_univ]
    simpa [L.range_eq_univ] using (L.contMDiffOn_symm (n := (⊤ : ℕ∞ω)))

/-- A continuous linear equivalence, packaged at analytic regularity. -/
private def continuousLinearEquivDiffeomorph
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : X ≃L[ℝ] Y) :
    Diffeomorph 𝓘(ℝ, X) 𝓘(ℝ, Y) X Y (⊤ : ℕ∞ω) where
  toEquiv := e.toLinearEquiv.toEquiv
  contMDiff_toFun := e.contDiff.contMDiff
  contMDiff_invFun := e.symm.contDiff.contMDiff

/-- The preferred extended chart, viewed as an analytic partial diffeomorphism. -/
private def preferredChartPartialDiffeomorph [IsManifold I (⊤ : ℕ∞ω) M]
    [I.Boundaryless] (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E (⊤ : ℕ∞ω) where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa [extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (n := (⊤ : ℕ∞ω)) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

/-- An analytic manifold map is analytic in preferred extended coordinates. -/
private lemma writtenInExtChartAt_contDiffOn
    [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) N]
    {F : M → N} {p : M} (hF : ContMDiff I J (⊤ : ℕ∞ω) F) :
    ContDiffOn ℝ (⊤ : ℕ∞ω) (writtenInExtChartAt I J p F : E → E')
      ((extChartAt I p).target ∩
        (F ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (F p)).source) := by
  let s : Set M := (extChartAt I p).source ∩ F ⁻¹' (extChartAt J (F p)).source
  have hs : s ⊆ (extChartAt I p).source := Set.inter_subset_left
  have hmaps : Set.MapsTo F s (extChartAt J (F p)).source := fun _ hx ↦ hx.2
  have hchart :
      ContDiffOn ℝ (⊤ : ℕ∞ω) (writtenInExtChartAt I J p F : E → E')
        ((extChartAt I p) '' s) :=
    (contMDiffOn_iff_of_subset_source' (I := I) (I' := J) (n := (⊤ : ℕ∞ω))
      (x := p) (y := F p) (f := F) hs hmaps).1 hF.contMDiffOn
  have himage :
      (extChartAt I p) '' s =
        ((extChartAt I p).target ∩
          (F ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (F p)).source) := by
    convert (extChartAt I p).image_source_inter_eq'
      (F ⁻¹' (extChartAt J (F p)).source) using 1 <;> ext x <;> rfl
  rwa [himage] at hchart

/-- An analytic map with injective manifold derivative has an analytic immersion normal form at
the point. -/
private theorem isImmersionAt_of_injective_mfderiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) N]
    [I.Boundaryless] [J.Boundaryless]
    {F : M → N} {p : M}
    (hF : ContMDiff I J (⊤ : ℕ∞ω) F)
    (hp : Function.Injective (mfderiv I J F p)) :
    IsImmersionAt I J (⊤ : ℕ∞ω) F p := by
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
  have hgΩ0 : ContDiffOn ℝ (⊤ : ℕ∞ω) g Ω0 := by
    simpa [g, Ω0] using writtenInExtChartAt_contDiffOn (I := I) (J := J) hF
  have hγΩ : ContDiffOn ℝ (⊤ : ℕ∞ω) γ Ω := by
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
  have hγAt : ContDiffAt ℝ (⊤ : ℕ∞ω) γ (a, (0 : G)) := hγΩ.contDiffAt hΩ
  have haInv : (fderiv ℝ γ (a, (0 : G))).IsInvertible := by
    rw [hγDeriv.fderiv]
    exact ⟨e, rfl⟩
  obtain ⟨Ψ, hbase, _hΨsub, hΨeq⟩ :=
    partialDiffeomorph_of_ift hΩ hγΩ hγAt hγDeriv haInv
  let C := preferredChartPartialDiffeomorph (I := J) (F p)
  let P : PartialDiffeomorph J J N H' (⊤ : ℕ∞ω) :=
    ((C.trans Ψ.symm).trans (continuousLinearEquivDiffeomorph e).toPartialDiffeomorph).trans
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
  have hcod : codChart ∈ IsManifold.maximalAtlas J (⊤ : ℕ∞ω) N :=
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
  have hdom : domChart ∈ IsManifold.maximalAtlas I (⊤ : ℕ∞ω) M :=
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
  exact (IsImmersionAtOfComplement.mk_of_continuousAt
    (I := I) (J := J) (n := (⊤ : ℕ∞ω)) hF.continuous.continuousAt e
    domChart codChart hdomp hcodp hdom hcod hwritten).isImmersionAt

/-- The complement of a finite-dimensional pointwise immersion is finite-dimensional. -/
private lemma finiteDimensional_complement
    [FiniteDimensional ℝ E'] {F : M → N} {p : M}
    (h : IsImmersionAt I J (⊤ : ℕ∞ω) F p) :
    FiniteDimensional ℝ h.complement := by
  let e := h.isImmersionAtOfComplement_complement.equiv
  haveI : FiniteDimensional ℝ (E × h.complement) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  exact FiniteDimensional.of_injective
    (LinearMap.inr ℝ E h.complement) LinearMap.inr_injective

/-- The pointwise immersion complement has the expected dimension. -/
private lemma finrank_prod_complement
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {F : M → N} {p : M}
    (h : IsImmersionAt I J (⊤ : ℕ∞ω) F p) :
    Module.finrank ℝ E + Module.finrank ℝ h.complement = Module.finrank ℝ E' := by
  let e := h.isImmersionAtOfComplement_complement.equiv
  letI : FiniteDimensional ℝ h.complement := finiteDimensional_complement h
  have hsum : Module.finrank ℝ (E × h.complement) =
      Module.finrank ℝ E + Module.finrank ℝ h.complement := Module.finrank_prod
  have heq : Module.finrank ℝ (E × h.complement) = Module.finrank ℝ E' :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  exact hsum.symm.trans heq

/-- Analytic derivative criterion for immersions between finite-dimensional boundaryless
manifolds. -/
theorem isImmersion_of_injective_mfderiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) N]
    [I.Boundaryless] [J.Boundaryless]
    {F : M → N} (hF : ContMDiff I J (⊤ : ℕ∞ω) F)
    (h : ∀ p : M, Function.Injective (mfderiv I J F p)) :
    IsImmersion I J (⊤ : ℕ∞ω) F := by
  classical
  by_cases hEmpty : IsEmpty M
  · exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ (IsEmpty.false x).elim⟩
  obtain ⟨p0⟩ := not_isEmpty_iff.mp hEmpty
  let h0 := isImmersionAt_of_injective_mfderiv hF (h p0)
  let G0 := h0.complement
  refine ⟨G0, inferInstance, inferInstance, ?_⟩
  intro p
  let hp := isImmersionAt_of_injective_mfderiv hF (h p)
  letI : FiniteDimensional ℝ hp.complement := finiteDimensional_complement hp
  letI : FiniteDimensional ℝ G0 := finiteDimensional_complement h0
  have hEq : Module.finrank ℝ hp.complement = Module.finrank ℝ G0 :=
    Nat.add_left_cancel
      ((finrank_prod_complement hp).trans (finrank_prod_complement h0).symm)
  let eG : hp.complement ≃L[ℝ] G0 := ContinuousLinearEquiv.ofFinrankEq hEq
  exact hp.isImmersionAtOfComplement_complement.trans_F eG

end AnalyticOrthogonalFiberImmersion
