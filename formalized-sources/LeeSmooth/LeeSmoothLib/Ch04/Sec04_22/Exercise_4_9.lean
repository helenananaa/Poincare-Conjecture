import Mathlib
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch04.Sec04_27.Problem_4_1
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; local precedents used:
-- `Proposition_4_8`, `Problem_4_1`, and mathlib's interior/boundary API for local diffeomorphisms.

open scoped Manifold ContDiff
open Manifold

universe uM uN

section TargetBoundary

variable {m n : ℕ} [NeZero n]
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n) N]
  [IsManifold (𝓡∂ n) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "J_n" => 𝓡∂ n

/-- Helper for Exercise 4.9: at a fixed point, an immersion and smooth submersion into a target
with boundary have invertible manifold derivative. -/
lemma mfderiv_isInvertible_of_immersion_and_submersion_target_boundary_point
    {F : M → N} (hFimm : IsImmersion I_m J_n ∞ F) (hFsubm : IsSmoothSubmersion I_m J_n F)
    (p : M) :
    (mfderiv I_m J_n F p).IsInvertible := by
  letI : NormedAddCommGroup (TangentSpace I_m p) := by
    change NormedAddCommGroup (EuclideanSpace ℝ (Fin m))
    infer_instance
  letI : NormedSpace ℝ (TangentSpace I_m p) := by
    change NormedSpace ℝ (EuclideanSpace ℝ (Fin m))
    infer_instance
  letI : CompleteSpace (TangentSpace I_m p) := by
    change CompleteSpace (EuclideanSpace ℝ (Fin m))
    infer_instance
  letI : NormedAddCommGroup (TangentSpace J_n (F p)) := by
    change NormedAddCommGroup (EuclideanSpace ℝ (Fin n))
    infer_instance
  letI : NormedSpace ℝ (TangentSpace J_n (F p)) := by
    change NormedSpace ℝ (EuclideanSpace ℝ (Fin n))
    infer_instance
  letI : CompleteSpace (TangentSpace J_n (F p)) := by
    change CompleteSpace (EuclideanSpace ℝ (Fin n))
    infer_instance
  -- The immersion/submersion characterizations give pointwise injectivity and surjectivity.
  have hinj : Function.Injective (mfderiv I_m J_n F p) :=
    hFimm.mfderiv_injective p
  have hsurj : Function.Surjective (mfderiv I_m J_n F p) :=
    hFsubm.surjective_mfderiv p
  -- A bijective continuous linear map between the tangent spaces is invertible.
  exact ContinuousLinearMap.isInvertible_of_bijective hinj hsurj

/-- A local diffeomorphism from a boundaryless Euclidean-model manifold is an immersion at each
point, even when the target model has a boundary.  The target chart is restricted to the actual
interior patch around the image point before it is extended to the ambient Euclidean model. -/
lemma is_local_diffeomorph_isImmersionAtOfComplement_target_boundary
    {F : M → N} (hF : IsLocalDiffeomorph I_m J_n ∞ F) (p : M) :
    IsImmersionAtOfComplement (PUnit.{uN + 1}) I_m J_n ∞ F p := by
  let hp := hF p
  let eT := hp.mfderivToContinuousLinearEquiv (by simp)
  let e0 : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin n) := by
    change EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin n) at eT
    exact eT
  let c : OpenPartialHomeomorph N (EuclideanHalfSpace n) := chartAt _ (F p)
  let C := c.extend J_n
  let t : Set (EuclideanSpace ℝ (Fin n)) := interior C.target
  have ht : IsOpen t := isOpen_interior
  have htarget_restr : (C.restr (C ⁻¹' t)).target = t := by
    rw [PartialEquiv.restr_target]
    ext y
    constructor
    · intro hy
      have hy' := hy.2
      change C (C.symm y) ∈ t at hy'
      rw [C.right_inv hy.1] at hy'
      exact hy'
    · intro hy
      refine ⟨interior_subset hy, ?_⟩
      change C (C.symm y) ∈ t
      rw [C.right_inv (interior_subset hy)]
      exact hy
  let cE : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n)) :=
    { toPartialEquiv := C.restr (C ⁻¹' t)
      open_source := by
        simpa [C] using c.isOpen_extend_preimage' ht
      open_target := by
        rw [htarget_restr]
        exact ht
      continuousOn_toFun := by
        exact c.continuousOn_extend.mono Set.inter_subset_left
      continuousOn_invFun := by
        exact c.continuousOn_extend_symm.mono (by
          intro y hy
          exact hy.1) }
  have hcE_target : cE.target = t := by
    exact htarget_restr
  have htarget : (𝓡∂ n).IsInteriorPoint (F p) :=
    (hp.isInteriorPoint_iff (by simp)).mp BoundarylessManifold.isInteriorPoint
  have hcp : F p ∈ c.source := mem_chart_source _ _
  have hCp : C (F p) ∈ interior C.target := by
    exact c.mem_interior_extend_target (c.map_source hcp)
      (show J_n (c (F p)) ∈ interior (Set.range J_n) from htarget)
  have hcEp : F p ∈ cE.source := by
    rw [show cE.source = C.source ∩ C ⁻¹' t by rfl]
    exact ⟨by simpa [C], hCp⟩
  obtain ⟨Φ, hpΦ, hΦ⟩ := hp
  let A : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    Φ.toOpenPartialHomeomorph.trans cE
  let R := e0.symm.toHomeomorph.toOpenPartialHomeomorph
  let domChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m)) := A.trans R
  have hpA : p ∈ A.source := by
    refine ⟨hpΦ, ?_⟩
    change Φ.toOpenPartialHomeomorph p ∈ cE.source
    rw [show Φ.toOpenPartialHomeomorph p = F p by exact (hΦ hpΦ).symm]
    exact hcEp
  have hpDom : p ∈ domChart.source := by
    simpa [domChart, R, A] using hpA
  have hcodChart : c ∈ IsManifold.maximalAtlas J_n ∞ N :=
    IsManifold.chart_mem_maximalAtlas _
  have hdomChart : domChart ∈ IsManifold.maximalAtlas I_m ∞ M := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn domChart
    · have hcE_to : ContMDiffOn J_n (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          cE cE.source := by
        simpa [cE, C] using
          (c.contMDiffOn_extend hcodChart).mono (by
            intro x hx
            exact hx.1)
      have hA_to : ContMDiffOn I_m (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          A A.source := by
        simpa [A, OpenPartialHomeomorph.coe_trans,
          PartialDiffeomorph.toOpenPartialHomeomorph] using
          hcE_to.comp' Φ.contMDiffOn_toFun
      have hR_to : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I_m ∞
          R R.source := by
        simpa [R] using e0.symm.contDiff.contMDiff.contMDiffOn
      simpa [domChart, OpenPartialHomeomorph.coe_trans] using hR_to.comp' hA_to
    · have hcE_inv : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) J_n ∞
          cE.symm cE.target := by
        have hsubset : cE.target ⊆ C.target := by
          rw [hcE_target]
          exact interior_subset
        have hsubset' : cE.target ⊆ J_n '' c.target := by
          intro y hy
          have hyC : y ∈ C.target := hsubset hy
          rw [show C = c.extend J_n by rfl, OpenPartialHomeomorph.extend_target] at hyC
          exact ⟨(𝓡∂ n).symm y, hyC.1, (𝓡∂ n).right_inv hyC.2⟩
        have hCEinv : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) J_n ∞
            C.symm cE.target :=
          (contMDiffOn_extend_symm hcodChart).mono hsubset'
        simpa [cE, C] using hCEinv
      have hA_inv : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I_m ∞
          A.symm A.target := by
        simpa [A, OpenPartialHomeomorph.coe_trans,
          PartialDiffeomorph.toOpenPartialHomeomorph] using
          Φ.contMDiffOn_invFun.comp' hcE_inv
      have hR_inv : ContMDiffOn I_m (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          R.symm R.target := by
        simpa [R] using e0.contDiff.contMDiff.contMDiffOn
      simpa [domChart, OpenPartialHomeomorph.coe_trans] using hA_inv.comp' hR_inv
  have hsource : domChart.source ⊆ F ⁻¹' c.source := by
    intro x hx
    have hxDom : x ∈ A.source ∩ A ⁻¹' R.source := by
      simpa [domChart] using hx
    have hxA : x ∈ A.source := hxDom.1
    have hxA' : x ∈ Φ.source ∩ Φ.toPartialEquiv ⁻¹' cE.source := by
      simpa [A] using hxA
    have hxΦ : x ∈ Φ.source := hxA'.1
    have hxC : Φ.toPartialEquiv x ∈ cE.source := hxA'.2
    have hxC' : Φ.toPartialEquiv x ∈ c.source := by
      simpa [C] using hxC.1
    change F x ∈ c.source
    rw [show F x = Φ.toPartialEquiv x by exact hΦ hxΦ]
    exact hxC'
  have hEq : Set.EqOn ((c.extend J_n) ∘ F ∘ (domChart.extend I_m).symm)
      e0 (domChart.extend I_m).target := by
    intro z hz
    have hzDomTarget : z ∈ domChart.target := by
      simpa [OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe] using hz
    let x := domChart.symm z
    have hxDom : x ∈ domChart.source := by
      dsimp [x]
      exact domChart.map_target hzDomTarget
    have hxDom' : x ∈ A.source ∩ A ⁻¹' R.source := by
      simpa [domChart] using hxDom
    have hxA : x ∈ Φ.source ∩ Φ.toPartialEquiv ⁻¹' cE.source := by
      simpa [A] using hxDom'.1
    have hxΦ : x ∈ Φ.source := hxA.1
    have hzDom : domChart x = z := by
      dsimp [x]
      exact domChart.right_inv hzDomTarget
    have hzA : e0 z = A x := by
      have hdom_apply : domChart x = e0.symm (A x) := by
        simp [domChart, A, R, OpenPartialHomeomorph.coe_trans]
      calc
        e0 z = e0 (domChart x) := by rw [hzDom]
        _ = e0 (e0.symm (A x)) := by rw [hdom_apply]
        _ = A x := e0.apply_symm_apply _
    have hext_symm : (domChart.extend I_m).symm z = x := by
      simp [x]
    calc
      ((c.extend J_n) ∘ F ∘ (domChart.extend I_m).symm) z =
          C (F x) := by
            change C (F ((domChart.extend I_m).symm z)) = C (F x)
            rw [hext_symm]
      _ = C (Φ.toPartialEquiv x) := by rw [hΦ hxΦ]
      _ = cE (Φ.toPartialEquiv x) := by rfl
      _ = A x := by
        change cE (Φ.toPartialEquiv x) = cE (Φ.toPartialEquiv x)
        rfl
      _ = e0 z := hzA.symm
  let prodEquiv :
      (EuclideanSpace ℝ (Fin m) × PUnit.{uN + 1}) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin m))
      PUnit.{uN + 1}).trans e0
  refine IsImmersionAtOfComplement.mk_of_charts
    (I := I_m) (J := J_n) (n := ∞) (f := F) (x := p) (F := PUnit.{uN + 1})
    prodEquiv domChart c hpDom (mem_chart_source _ _) hdomChart hcodChart hsource ?_
  simpa [Function.comp_def, prodEquiv, ContinuousLinearEquiv.prodUnique] using hEq

/-- Exercise 4.9 (1): Proposition 4.8 (1) still holds when the target `N` is allowed to be a
smooth manifold with boundary, while the source `M` remains boundaryless. -/
theorem is_local_diffeomorph_iff_is_immersion_and_is_smooth_submersion_target_boundary
    {F : M → N} :
    IsLocalDiffeomorph I_m J_n ∞ F ↔
      IsImmersion I_m J_n ∞ F ∧ IsSmoothSubmersion I_m J_n F := by
  refine ⟨?_, ?_⟩
  · intro hF
    let hcomp : IsImmersionOfComplement (PUnit.{uN + 1}) I_m J_n ∞ F :=
      fun p ↦ is_local_diffeomorph_isImmersionAtOfComplement_target_boundary hF p
    exact ⟨hcomp.isImmersion, hF.isSmoothSubmersion⟩
  · rintro ⟨hFimm, hFsubm⟩
    have hSmooth : ContMDiff I_m J_n ∞ F := hFsubm.contMDiff
    intro p
    -- The boundaryless source gives an interior image point for the inverse function theorem.
    have hInv : (mfderiv I_m J_n F p).IsInvertible :=
      mfderiv_isInvertible_of_immersion_and_submersion_target_boundary_point hFimm hFsubm p
    exact isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
      (I := I_m) (J := J_n) (n := ∞) (by simp)
      BoundarylessManifold.isInteriorPoint hSmooth hInv

/-- The target-boundary formulation available without a boundaryless target-model instance. -/
theorem is_local_diffeomorph_iff_is_mfderiv_injective_and_is_smooth_submersion_target_boundary
    {F : M → N} :
    IsLocalDiffeomorph I_m J_n ∞ F ↔
      (∀ p : M, Function.Injective (mfderiv I_m J_n F p)) ∧
        IsSmoothSubmersion I_m J_n F := by
  refine ⟨fun hF ↦ ⟨?_, hF.isSmoothSubmersion⟩, ?_⟩
  · intro p
    exact (hF.mfderivToContinuousLinearEquiv (by simp) p).injective
  · rintro ⟨hinj, hFsubm⟩
    have hSmooth : ContMDiff I_m J_n ∞ F := hFsubm.contMDiff
    intro p
    letI : NormedAddCommGroup (TangentSpace I_m p) := by
      change NormedAddCommGroup (EuclideanSpace ℝ (Fin m))
      infer_instance
    letI : NormedSpace ℝ (TangentSpace I_m p) := by
      change NormedSpace ℝ (EuclideanSpace ℝ (Fin m))
      infer_instance
    letI : CompleteSpace (TangentSpace I_m p) := by
      change CompleteSpace (EuclideanSpace ℝ (Fin m))
      infer_instance
    letI : NormedAddCommGroup (TangentSpace J_n (F p)) := by
      change NormedAddCommGroup (EuclideanSpace ℝ (Fin n))
      infer_instance
    letI : NormedSpace ℝ (TangentSpace J_n (F p)) := by
      change NormedSpace ℝ (EuclideanSpace ℝ (Fin n))
      infer_instance
    letI : CompleteSpace (TangentSpace J_n (F p)) := by
      change CompleteSpace (EuclideanSpace ℝ (Fin n))
      infer_instance
    have hInv : (mfderiv I_m J_n F p).IsInvertible :=
      ContinuousLinearMap.isInvertible_of_bijective
        (A := mfderiv I_m J_n F p) (hinj p) (hFsubm.surjective_mfderiv p)
    exact isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
      (I := I_m) (J := J_n) (n := ∞) (by simp)
      BoundarylessManifold.isInteriorPoint hSmooth hInv

/-- Exercise 4.9 (2): if the source is boundaryless, then Proposition 4.8 (2) still holds when the
target is a smooth manifold with boundary of the same dimension. -/
theorem is_local_diffeomorph_of_is_immersion_of_eq_dim_target_boundary {F : M → N}
    (hmn : m = n) (hF : IsImmersion I_m J_n ∞ F) :
    IsLocalDiffeomorph I_m J_n ∞ F :=
  hF.isLocalDiffeomorph_of_eq_finrank (by
    simpa [finrank_euclideanSpace_fin] using hmn)

/-- Exercise 4.9 (3): if the source is boundaryless, then Proposition 4.8 (3) still holds when the
target is a smooth manifold with boundary of the same dimension. -/
theorem is_local_diffeomorph_of_is_smooth_submersion_of_eq_dim_target_boundary {F : M → N}
    (hmn : m = n) (hF : IsSmoothSubmersion I_m J_n F) :
    IsLocalDiffeomorph I_m J_n ∞ F :=
  hF.isLocalDiffeomorph_of_eq_finrank (by
    simpa [finrank_euclideanSpace_fin] using hmn)

end TargetBoundary

section SourceBoundary

variable (n : ℕ) [NeZero n]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Exercise 4.9: the manifold derivative of the half-space inclusion is the identity
at every point of the half-space model. -/
lemma euclidean_half_space_inclusion_mfderiv_eq_id (p : EuclideanHalfSpace n) :
    mfderiv (𝓡∂ n) (𝓡 n) (EuclideanHalfSpace.inclusion n) p =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ n) p) := by
  -- The inclusion is the model-with-corners map itself, so its derivative is the model identity.
  change mfderiv (𝓡∂ n) (𝓡 n) (𝓡∂ n) p =
    ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ n) p)
  simpa using ((𝓡∂ n).hasMFDerivAt (x := p)).mfderiv

set_option backward.isDefEq.respectTransparency false in
/-- Exercise 4.9 (4): Proposition 4.8 (2) fails if the source manifold is allowed to have
boundary; the canonical inclusion `ℍ^n ↪ ℝ^n` is a same-dimensional smooth immersion, but it is
not a local diffeomorphism. -/
theorem euclidean_half_space_inclusion_is_immersion_not_local_diffeomorph :
    IsImmersion (𝓡∂ n) (𝓡 n) ∞ (EuclideanHalfSpace.inclusion n) ∧
      ¬ IsLocalDiffeomorph (𝓡∂ n) (𝓡 n) ∞ (EuclideanHalfSpace.inclusion n) := by
  refine ⟨?_, euclideanHalfSpace_inclusion_not_isLocalDiffeomorph n⟩
  refine ⟨PUnit, inferInstance, inferInstance, ?_⟩
  intro p
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (I := 𝓡∂ n) (J := 𝓡 n) (n := ∞) (𝓡∂ n).continuousAt
    (.prodUnique ℝ _ _) (.refl _) (.refl _) (by simp) (by simp)
    (IsManifold.subset_maximalAtlas (by simp))
    (IsManifold.subset_maximalAtlas (by simp))
  intro x hx
  change (𝓡 n) ((𝓡 n).symm ((𝓡∂ n) ((𝓡∂ n).symm x))) = x
  rw [(𝓡∂ n).right_inv (by simp_all), (𝓡 n).right_inv (by simp)]

end SourceBoundary
