import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import LeeSmoothLib.Ch05.Sec05_35.Notation_5_35_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold Topology
open Manifold Set Function

set_option backward.isDefEq.respectTransparency false

universe uE uE' uH uH' uM

section ExtendMfderivInvertible

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
/-- The extended chart of a maximal-atlas chart is manifold-differentiable on its source. -/
lemma mdifferentiableAt_extend_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) :
    MDifferentiableAt I 𝓘(ℝ, E) (e.extend I) x :=
  (e.contMDiffAt_extend he hx).mdifferentiableAt (by simp)

omit [IsManifold I ∞ M] in
/-- The inverse of an extended maximal-atlas chart is differentiable within `range I`
on the extended target. -/
lemma mdifferentiableWithinAt_extend_symm_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {z : E} (hz : z ∈ (e.extend I).target) :
    MDifferentiableWithinAt 𝓘(ℝ, E) I (e.extend I).symm (range I) z := by
  have hz_range : z ∈ range I := e.extend_target_subset_range (I := I) hz
  have hI : MDifferentiableWithinAt 𝓘(ℝ, E) I I.symm (range I) z :=
    I.mdifferentiableWithinAt_symm hz_range
  have hz_target : I.symm z ∈ e.target := by
    have hz' : z ∈ (e.extend I).target := hz
    rw [e.extend_target (I := I)] at hz'
    exact hz'.1
  have he_symm : MDifferentiableAt I I e.symm (I.symm z) :=
    (contMDiffAt_symm_of_mem_maximalAtlas he hz_target).mdifferentiableAt (by simp)
  have hcomp :=
    he_symm.comp_mdifferentiableWithinAt_of_eq (f := I.symm) (s := range I) (x := z)
      hI rfl
  simpa [OpenPartialHomeomorph.extend_coe_symm] using hcomp

omit [IsManifold I ∞ M] in
/-- The derivative of an extended chart, post-composed with the derivative of its inverse within
`range I`, is the identity on the model space. -/
lemma mfderiv_extend_comp_mfderivWithin_extend_symm
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {y : E} (hy : y ∈ (e.extend I).target) :
    (mfderiv I 𝓘(ℝ, E) (e.extend I) ((e.extend I).symm y)) ∘L
      (mfderivWithin 𝓘(ℝ, E) I (e.extend I).symm (range I) y) =
        ContinuousLinearMap.id ℝ _ := by
  have U : UniqueMDiffWithinAt 𝓘(ℝ, E) (range I) y := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact I.uniqueDiffOn _ (e.extend_target_subset_range (I := I) hy)
  have h'y : (e.extend I).symm y ∈ (e.extend I).source := (e.extend I).map_target hy
  have h''y : (e.extend I).symm y ∈ e.source := by
    rwa [e.extend_source (I := I)] at h'y
  rw [← mfderiv_comp_mfderivWithin]; rotate_left
  · exact mdifferentiableAt_extend_of_mem_maximalAtlas he h''y
  · exact mdifferentiableWithinAt_extend_symm_of_mem_maximalAtlas he hy
  · exact U
  rw [← mfderivWithin_id U]
  apply Filter.EventuallyEq.mfderivWithin_eq
  · have hnhds : (e.extend I).target ∈ 𝓝[range I] y := by
      rw [e.extend_target' (I := I)] at hy ⊢
      rcases hy with ⟨z, hz, rfl⟩
      exact I.image_mem_nhdsWithin (e.open_target.mem_nhds hz)
    filter_upwards [hnhds] with z hz
    simp only [Function.comp_def, PartialEquiv.right_inv (e.extend I) hz, id_eq]
  · simp only [Function.comp_def, PartialEquiv.right_inv (e.extend I) hy, id_eq]

omit [IsManifold I ∞ M] in
/-- The derivative of the inverse of an extended chart within `range I`, post-composed with the
derivative of the extended chart, is the identity on the tangent space. -/
lemma mfderivWithin_extend_symm_comp_mfderiv_extend
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {y : E} (hy : y ∈ (e.extend I).target) :
    (mfderivWithin 𝓘(ℝ, E) I (e.extend I).symm (range I) y) ∘L
      (mfderiv I 𝓘(ℝ, E) (e.extend I) ((e.extend I).symm y)) =
        ContinuousLinearMap.id ℝ _ := by
  have h'y : (e.extend I).symm y ∈ (e.extend I).source := (e.extend I).map_target hy
  have h''y : (e.extend I).symm y ∈ e.source := by
    rwa [e.extend_source (I := I)] at h'y
  have U' : UniqueMDiffWithinAt I (e.extend I).source ((e.extend I).symm y) :=
    (e.isOpen_extend_source (I := I)).uniqueMDiffWithinAt h'y
  have hmdiff : MDifferentiableAt I 𝓘(ℝ, E) (e.extend I) ((e.extend I).symm y) :=
    mdifferentiableAt_extend_of_mem_maximalAtlas he h''y
  have : mfderiv I 𝓘(ℝ, E) (e.extend I) ((e.extend I).symm y) =
      mfderivWithin I 𝓘(ℝ, E) (e.extend I) (e.extend I).source ((e.extend I).symm y) := by
    rw [mfderivWithin_eq_mfderiv U' hmdiff]
  rw [this, ← mfderivWithin_comp_of_eq]; rotate_left
  · exact mdifferentiableWithinAt_extend_symm_of_mem_maximalAtlas he hy
  · exact hmdiff.mdifferentiableWithinAt
  · intro z hz
    exact e.extend_target_subset_range (I := I) ((e.extend I).map_source hz)
  · exact U'
  · exact PartialEquiv.right_inv (e.extend I) hy
  rw [← mfderivWithin_id U']
  apply Filter.EventuallyEq.mfderivWithin_eq
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Function.comp_def, PartialEquiv.left_inv (e.extend I) hz, id_eq]
  · simp only [Function.comp_def, PartialEquiv.right_inv (e.extend I) hy, id_eq]

omit [IsManifold I ∞ M] in
/-- The manifold derivative of an extended maximal-atlas chart is invertible. -/
lemma isInvertible_mfderiv_extend_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) :
    (mfderiv I 𝓘(ℝ, E) (e.extend I) x).IsInvertible := by
  have hx_source : x ∈ (e.extend I).source := by
    rwa [e.extend_source (I := I)]
  have hy : e.extend I x ∈ (e.extend I).target := (e.extend I).map_source hx_source
  have Z :=
    ContinuousLinearMap.IsInvertible.of_inverse
      (mfderiv_extend_comp_mfderivWithin_extend_symm he hy)
      (mfderivWithin_extend_symm_comp_mfderiv_extend he hy)
  have : (e.extend I).symm (e.extend I x) = x := (e.extend I).left_inv hx_source
  rwa [this] at Z

end ExtendMfderivInvertible

section SubmanifoldTangentSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E H}
variable {I : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I ∞ M]
variable (S : Set M) [ChartedSpace H S] [IsManifold J ∞ S]

-- Proof sketch: for the forward implication, compose a tangent vector in the range of the
-- inclusion differential with a smooth function whose restriction to `S` is zero. For the
-- converse, use the local normal-form characterization of a smooth embedding and test against
-- coordinate functions transverse to `S`.
omit [IsManifold J ∞ S] in
/-- Proposition 5.37: if `S ⊆ M` is given a smooth manifold structure for which the inclusion
`S ↪ M` is a smooth embedding, then an ambient tangent vector at `p ∈ S` is tangent to `S`
exactly when it annihilates every smooth real-valued function on `M` whose restriction to `S`
vanishes. -/
theorem tangentVector_mem_submanifold_iff_forall_smooth_eq_zero
    [FiniteDimensional ℝ E'] [T2Space M]
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → M))
    (p : S) (v : TangentSpace I (p : M)) :
    v ∈ T[J; p] ↔
      ∀ f : C^∞⟮I, M; ℝ⟯, EqOn f 0 S → mfderiv% f (p : M) v = 0 := by
  have hι_mdiff : MDifferentiableAt J I (Subtype.val : S → M) p :=
    (hS.contMDiff.mdifferentiable (by simp)) p
  constructor
  · intro hv f hf
    rw [show T[J; p] = (mfderiv J I (Subtype.val : S → M) p).range by rfl,
      LinearMap.mem_range] at hv
    rcases hv with ⟨w, rfl⟩
    have hf_comp : (f : M → ℝ) ∘ (Subtype.val : S → M) = fun _ : S ↦ (0 : ℝ) := by
      ext q
      exact hf q.property
    have hf_mdiff : MDifferentiableAt I 𝓘(ℝ) (f : M → ℝ) (p : M) :=
      f.contMDiff.mdifferentiable (by simp) (p : M)
    have hchain :=
      mfderiv_comp_apply (I := J) (I' := I) (I'' := 𝓘(ℝ))
        (g := (f : M → ℝ)) (f := (Subtype.val : S → M)) (x := p)
        hf_mdiff hι_mdiff w
    have hconst :
        mfderiv J 𝓘(ℝ) ((f : M → ℝ) ∘ (Subtype.val : S → M)) p =
          mfderiv J 𝓘(ℝ) (fun _ : S ↦ (0 : ℝ)) p := by
      rw [hf_comp]
    have hzero : mfderiv J 𝓘(ℝ) (fun _ : S ↦ (0 : ℝ)) p w = 0 := by
      simp [mfderiv_const]
    exact hzero ▸ (hconst ▸ hchain.symm)
  · intro hv
    let hι : IsImmersionAt J I ∞ (Subtype.val : S → M) p := hS.isImmersion.isImmersionAt p
    let πF : E' →L[ℝ] hι.complement :=
      (ContinuousLinearMap.snd ℝ E hι.complement).comp hι.equiv.symm.toContinuousLinearMap
    let L : E →L[ℝ] E' :=
      hι.equiv.toContinuousLinearMap.comp
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] hι.complement))
    have hslice : ∀ q : S, q ∈ hι.domChart.source →
        (hι.codChart.extend I) (q : M) = hι.equiv ((hι.domChart.extend J) q, (0 : hι.complement)) := by
      intro q hq
      have hq_source : q ∈ (hι.domChart.extend J).source := by
        simpa [hι.domChart.extend_source (I := J)] using hq
      have hq_target : (hι.domChart.extend J) q ∈ (hι.domChart.extend J).target :=
        (hι.domChart.extend J).map_source hq_source
      have hcoords := hι.writtenInCharts hq_target
      have hq_left : (hι.domChart.extend J).symm ((hι.domChart.extend J) q) = q :=
        (hι.domChart.extend J).left_inv hq_source
      simp only [Function.comp_apply] at hcoords
      rwa [hq_left] at hcoords
    have hπ_zero : ∀ q : S, q ∈ hι.domChart.source →
        πF ((hι.codChart.extend I) (q : M)) = 0 := by
      intro q hq
      rw [hslice q hq]
      simp [πF]
    rcases Topology.IsInducing.subtypeVal.isOpen_iff.mp hι.domChart.open_source with
      ⟨W, hWopen, hWeq⟩
    have hpW : (p : M) ∈ W := by
      have : p ∈ (Subtype.val : S → M) ⁻¹' W := by
        rw [hWeq]
        exact hι.mem_domChart_source
      exact this
    let U : Set M := W ∩ hι.codChart.source
    have hUopen : IsOpen U := hWopen.inter hι.codChart.open_source
    have hpU : (p : M) ∈ U := ⟨hpW, hι.mem_codChart_source⟩
    obtain ⟨φ, -, hφsupp⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := I) (p : M)).mem_iff.mp
        (hUopen.mem_nhds hpU)
    have hφ1 : (φ : M → ℝ) =ᶠ[𝓝 (p : M)] 1 := φ.eventuallyEq_one
    have hcod_mdiff :
        MDifferentiableAt I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M) :=
      mdifferentiableAt_extend_of_mem_maximalAtlas hι.codChart_mem_maximalAtlas
        hι.mem_codChart_source
    have hdom_mdiff :
        MDifferentiableAt J 𝓘(ℝ, E) (hι.domChart.extend J) p :=
      mdifferentiableAt_extend_of_mem_maximalAtlas hι.domChart_mem_maximalAtlas
        hι.mem_domChart_source
    have hcod_inv :
        (mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M)).IsInvertible :=
      isInvertible_mfderiv_extend_of_mem_maximalAtlas hι.codChart_mem_maximalAtlas
        hι.mem_codChart_source
    have hdom_inv :
        (mfderiv J 𝓘(ℝ, E) (hι.domChart.extend J) p).IsInvertible :=
      isInvertible_mfderiv_extend_of_mem_maximalAtlas hι.domChart_mem_maximalAtlas
        hι.mem_domChart_source
    have hπv : πF (mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M) v) = 0 := by
      refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) (V := hι.complement) ?_
      intro μ
      let g : M → ℝ := (μ.comp πF : E' → ℝ) ∘ (hι.codChart.extend I)
      have hg_on : ContMDiffOn I 𝓘(ℝ) ∞ g hι.codChart.source := by
        have hπμ : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ) ∞ (μ.comp πF : E' → ℝ) :=
          (μ.comp πF).contDiff.contMDiff
        exact hπμ.comp_contMDiffOn
          (hι.codChart.contMDiffOn_extend hι.codChart_mem_maximalAtlas)
      have hg_zero : ∀ q : S, (q : M) ∈ U → g q = 0 := by
        intro q hqU
        have hqW : (q : M) ∈ W := hqU.1
        have hq_dom : q ∈ hι.domChart.source := by
          have : q ∈ (Subtype.val : S → M) ⁻¹' W := hqW
          rwa [hWeq] at this
        have hgq := hπ_zero q hq_dom
        change μ (πF ((hι.codChart.extend I) (q : M))) = 0
        rw [hgq, map_zero]
      let Ftest : M → ℝ := fun x ↦ φ x • g x
      have hF_tsupp : tsupport Ftest ⊆ U :=
        (tsupport_smul_subset_left (fun x ↦ φ x) g).trans hφsupp
      have hF_smooth : ContMDiff I 𝓘(ℝ) ∞ Ftest := by
        refine contMDiff_of_tsupport fun x hx ↦ ?_
        have hxU : x ∈ U := hF_tsupp hx
        have hgAt : ContMDiffAt I 𝓘(ℝ) ∞ g x :=
          (hg_on x hxU.2).contMDiffAt (hι.codChart.open_source.mem_nhds hxU.2)
        exact φ.contMDiffAt.smul hgAt
      have hF_vanishes : EqOn Ftest 0 S := by
        intro x hxS
        by_cases hxU : x ∈ U
        · have : g x = 0 := hg_zero ⟨x, hxS⟩ hxU
          simp [Ftest, this]
        · have hx_not : x ∉ tsupport φ := fun h ↦ hxU (hφsupp h)
          have hx_not' : x ∉ tsupport Ftest := fun h ↦ hx_not <|
            (tsupport_smul_subset_left (fun y ↦ φ y) g) h
          exact image_eq_zero_of_notMem_tsupport hx_not'
      have hF_eq_g : Ftest =ᶠ[𝓝 (p : M)] g := by
        filter_upwards [hφ1] with x hx
        simp [Ftest, hx]
      let f : C^∞⟮I, M; ℝ⟯ := ⟨Ftest, hF_smooth⟩
      have hdf : mfderiv I 𝓘(ℝ) (f : M → ℝ) (p : M) v = 0 := hv f hF_vanishes
      have hg_mdiff : MDifferentiableAt I 𝓘(ℝ) g (p : M) :=
        (hg_on (p : M) hpU.2).mdifferentiableWithinAt (by simp : (∞ : ℕ∞ω) ≠ 0)
          |>.mdifferentiableAt (hι.codChart.open_source.mem_nhds hpU.2)
      have hdf_eq : mfderiv I 𝓘(ℝ) Ftest (p : M) = mfderiv I 𝓘(ℝ) g (p : M) :=
        hF_eq_g.mfderiv_eq
      have hμπ : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ) (μ.comp πF : E' → ℝ)
          (hι.codChart.extend I (p : M)) :=
        (μ.comp πF).mdifferentiableAt
      have hμπ_eq :
          mfderiv 𝓘(ℝ, E') 𝓘(ℝ) (μ.comp πF : E' → ℝ)
            (hι.codChart.extend I (p : M)) = μ.comp πF :=
        ContinuousLinearMap.mfderiv_eq (μ.comp πF)
      have hchain_g :
          mfderiv I 𝓘(ℝ) g (p : M) v =
            (μ.comp πF) (mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M) v) := by
        have hcomp :=
          mfderiv_comp_apply (I := I) (I' := 𝓘(ℝ, E')) (I'' := 𝓘(ℝ))
            (g := (μ.comp πF : E' → ℝ)) (f := (hι.codChart.extend I : M → E'))
            (x := (p : M)) hμπ hcod_mdiff v
        rw [hμπ_eq] at hcomp
        exact hcomp
      have : (μ.comp πF) (mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M) v) = 0 := by
        rw [← hchain_g, ← hdf_eq]
        exact hdf
      simpa using this
    have hL_eq : ∀ q : S, q ∈ hι.domChart.source →
        (hι.codChart.extend I ∘ Subtype.val) q = (L ∘ hι.domChart.extend J) q := by
      intro q hq
      rw [Function.comp_apply, Function.comp_apply, hslice q hq]
      simp [L]
    have hL_eqOn :
        EqOn (hι.codChart.extend I ∘ (Subtype.val : S → M))
          (↑L ∘ hι.domChart.extend J) hι.domChart.source := hL_eq
    have hL_eventually :
        (hι.codChart.extend I ∘ (Subtype.val : S → M)) =ᶠ[𝓝 p]
          (↑L ∘ hι.domChart.extend J) :=
      hL_eqOn.eventuallyEq_of_mem
        (hι.domChart.open_source.mem_nhds hι.mem_domChart_source)
    have hcomp_ι :
        mfderiv J 𝓘(ℝ, E') (hι.codChart.extend I ∘ (Subtype.val : S → M)) p =
          (mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M)).comp
            (mfderiv J I (Subtype.val : S → M) p) :=
      mfderiv_comp p
        (by simpa using hcod_mdiff) hι_mdiff
    have hcomp_L :
        mfderiv J 𝓘(ℝ, E') ((↑L : E → E') ∘ hι.domChart.extend J) p =
          L.comp (mfderiv J 𝓘(ℝ, E) (hι.domChart.extend J) p) := by
      have hL_mdiff :
          MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') (↑L : E → E')
            (hι.domChart.extend J p) := L.mdifferentiableAt
      have hL_deriv :
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') (↑L : E → E') (hι.domChart.extend J p) = L :=
        ContinuousLinearMap.mfderiv_eq L
      rw [mfderiv_comp p hL_mdiff hdom_mdiff, hL_deriv]
    have hdiff :
        (mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M)).comp
            (mfderiv J I (Subtype.val : S → M) p) =
          L.comp (mfderiv J 𝓘(ℝ, E) (hι.domChart.extend J) p) := by
      have hEq :
          mfderiv J 𝓘(ℝ, E') (hι.codChart.extend I ∘ (Subtype.val : S → M)) p =
            mfderiv J 𝓘(ℝ, E') ((↑L : E → E') ∘ hι.domChart.extend J) p :=
        Filter.EventuallyEq.mfderiv_eq (I := J) (I' := 𝓘(ℝ, E')) hL_eventually
      exact hcomp_ι.symm.trans (hEq.trans hcomp_L)
    rw [show T[J; p] = (mfderiv J I (Subtype.val : S → M) p).range by rfl,
      LinearMap.mem_range]
    rcases hcod_inv with ⟨eM, heM⟩
    rcases hdom_inv with ⟨eS, heS⟩
    have hι_apply (w : TangentSpace J p) :
        mfderiv J I (Subtype.val : S → M) p w =
          eM.symm (L (eS w : E)) := by
      have hw := congrArg (fun G : TangentSpace J p →L[ℝ] E' ↦ G w) hdiff
      simp only [ContinuousLinearMap.comp_apply] at hw
      have hφ :
          (mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M)
              (mfderiv J I (Subtype.val : S → M) p w) : E') =
            L (mfderiv J 𝓘(ℝ, E) (hι.domChart.extend J) p w : E) := hw
      have h' : (eM (mfderiv J I (Subtype.val : S → M) p w) : E') =
          L (eS w : E) := by
        have h1 : (eM (mfderiv J I (Subtype.val : S → M) p w) : E') =
            (mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M)
              (mfderiv J I (Subtype.val : S → M) p w) : E') := by
          rw [← heM]; rfl
        have h2 : (mfderiv J 𝓘(ℝ, E) (hι.domChart.extend J) p w : E) = (eS w : E) := by
          rw [← heS]; rfl
        rw [h1, hφ, h2]
      exact (ContinuousLinearEquiv.eq_symm_apply eM).2 h'
    let wE : E :=
      (ContinuousLinearMap.fst ℝ E hι.complement)
        (hι.equiv.symm (mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M) v))
    have hLw : L wE = mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M) v := by
      have hpair :
          hι.equiv.symm (mfderiv I 𝓘(ℝ, E') (hι.codChart.extend I) (p : M) v) =
            (wE, (0 : hι.complement)) := by
        apply Prod.ext
        · rfl
        · exact hπv
      have hEq := congrArg (fun t ↦ hι.equiv t) hpair
      simpa [L, wE] using hEq.symm
    let wS : TangentSpace J p :=
      eS.symm (wE : TangentSpace 𝓘(ℝ, E) (hι.domChart.extend J p))
    refine ⟨wS, ?_⟩
    have hwS := hι_apply wS
    change (mfderiv J I (Subtype.val : S → M) p) wS = v
    rw [hwS]
    have hEwS : (eS wS : E) = wE := by
      have h :=
        eS.apply_symm_apply (wE : TangentSpace 𝓘(ℝ, E) (hι.domChart.extend J p))
      exact h
    rw [hEwS]
    have hLv : L wE = (eM v : E') := by
      rw [hLw, ← heM]
      rfl
    rw [hLv]
    simp

end SubmanifoldTangentSpace
