import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Algebra.SMul
import LeeSmoothLib.Ch01.Sec01_04.Example_1_33
import LeeSmoothLib.Ch04.Sec04_26.Example_4_35
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

noncomputable section

/-- Each standard affine chart belongs to the canonical smooth maximal atlas of projective space. -/
private theorem problem_4_10_projectiveChart_mem_maximalAtlas (n : ℕ)
    (i : Fin (n + 1)) :
    realProjectiveChart n i ∈ IsManifold.maximalAtlas (𝓡 n) ∞ (RealProjectiveSpace n) := by
  apply IsManifold.subset_maximalAtlas
  change realProjectiveChart n i ∈
    { e | ∃ j : Fin (n + 1), e = realProjectiveChart n j }
  exact ⟨i, rfl⟩

/-- The source of a standard projective chart, packaged as an open submanifold. -/
private def problem_4_10_projectiveChartOpens (n : ℕ) (i : Fin (n + 1)) :
    TopologicalSpace.Opens (RealProjectiveSpace n) :=
  ⟨realProjectiveChartDomain n i, realProjectiveChartDomain_isOpen n i⟩

/-- The standard projective chart, restricted to its source, is smooth. -/
private theorem problem_4_10_projectiveChart_contMDiff (n : ℕ) (i : Fin (n + 1)) :
    ContMDiff (𝓡 n) (𝓡 n) ∞
      (fun x : problem_4_10_projectiveChartOpens n i ↦ realProjectiveChart n i x) := by
  intro x
  rw [contMDiffAt_subtype_iff]
  exact contMDiffAt_of_mem_maximalAtlas
    (problem_4_10_projectiveChart_mem_maximalAtlas n i) x.2

/-- In standard affine coordinates, the sphere quotient is the smooth coordinate-ratio map. -/
private theorem problem_4_10_quotient_contMDiff (n : ℕ) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereToRealProjectiveSpace n) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk finrank_euclideanSpace_fin
  intro y
  have hy_ne : ((y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0) :=
    unit_sphere_point_ne_zero n y
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1),
      ((y : EuclideanSpace ℝ (Fin (n + 1))) i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hy_ne
    ext j
    exact h j
  let ratio : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) :=
    fun z ↦ WithLp.toLp 2 (fun j ↦ z (i.succAbove j) / z i)
  have hratio_on :
      ContDiffOn ℝ ∞ ratio
        {z : EuclideanSpace ℝ (Fin (n + 1)) | z i ≠ 0} := by
    refine contDiffOn_piLp' (p := (2 : ENNReal)) ?_
    intro j
    exact
      (((contDiff_piLp_apply (p := (2 : ENNReal)) (i := i.succAbove j)) :
          ContDiff ℝ ∞
            (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z (i.succAbove j))).contDiffOn).div
        (((contDiff_piLp_apply (p := (2 : ENNReal)) (i := i)) :
          ContDiff ℝ ∞
            (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z i)).contDiffOn)
        (fun z hz ↦ hz)
  have hratio_at :
      ContDiffAt ℝ ∞ ratio (y : EuclideanSpace ℝ (Fin (n + 1))) := by
    apply hratio_on.contDiffAt
    have hopen :
        IsOpen {z : EuclideanSpace ℝ (Fin (n + 1)) | z i ≠ 0} := by
      simpa using
        isOpen_ne_fun
          ((PiLp.continuous_apply 2 _ i) :
            Continuous fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z i)
          continuous_const
    exact hopen.mem_nhds hi
  have hratio_sphere :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞
        (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦ ratio z) y := by
    exact hratio_at.contMDiffAt.comp y
      ((contMDiff_coe_sphere :
        ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞
          ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
            EuclideanSpace ℝ (Fin (n + 1)))) y)
  have hsymm :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞
        (realProjectiveChart n i).symm (ratio (y : EuclideanSpace ℝ (Fin (n + 1)))) := by
    simpa [ratio] using
      contMDiffAt_symm_of_mem_maximalAtlas
        (problem_4_10_projectiveChart_mem_maximalAtlas n i)
        (by simp : ratio (y : EuclideanSpace ℝ (Fin (n + 1))) ∈ Set.univ)
  have hcomp :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞
        ((realProjectiveChart n i).symm ∘
          fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦ ratio z) y :=
    hsymm.comp y hratio_sphere
  have hEq :
      sphereToRealProjectiveSpace n =ᶠ[nhds y]
        ((realProjectiveChart n i).symm ∘
          fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦ ratio z) := by
    have hopen :
        IsOpen {z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 |
          ((z : EuclideanSpace ℝ (Fin (n + 1))) i) ≠ 0} := by
      simpa using isOpen_ne_fun (unit_sphere_coordinate_continuous n i) continuous_const
    filter_upwards [hopen.mem_nhds hi] with z hz
    have hzDomain :
        sphereToRealProjectiveSpace n z ∈ realProjectiveChartDomain n i :=
      (sphereToRealProjectiveSpace_mem_realProjectiveChartDomain_iff n z i).2 hz
    have hleft := (realProjectiveChart n i).left_inv hzDomain
    have hformula : realProjectiveChart n i (sphereToRealProjectiveSpace n z) = ratio z := by
      simpa [sphereToRealProjectiveSpace, ratio] using
        (realProjectiveChart_mk n i
          (z : EuclideanSpace ℝ (Fin (n + 1))) (unit_sphere_point_ne_zero n z))
    rw [hformula] at hleft
    simpa [Function.comp] using hleft.symm
  exact hcomp.congr_of_eventuallyEq hEq

/-- In a projective chart, the distinguished homogeneous representative varies smoothly. -/
private theorem problem_4_10_chartLiftVector_contMDiff (n : ℕ) (i : Fin (n + 1)) :
    ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞
      (fun x : problem_4_10_projectiveChartOpens n i ↦
        sphereToRealProjectiveSpace_chart_lift_vector n i x) := by
  have hval :
      ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞
        (fun u : EuclideanSpace ℝ (Fin n) ↦ realProjectiveChartInvVector n i u) := by
    have hvec :
        ContDiff ℝ (⊤ : WithTop ℕ∞)
          (fun u : EuclideanSpace ℝ (Fin n) ↦ realProjectiveChartInvVector n i u) := by
      refine contDiff_piLp' (p := (2 : ENNReal)) ?_
      intro l
      exact realProjectiveChartInvVector_coordinate_contDiff n i l
    exact hvec.contMDiff.of_le (by simp)
  convert hval.comp (problem_4_10_projectiveChart_contMDiff n i) using 1
  funext x
  rfl

/-- Normalizing the standard homogeneous representative gives a smooth sphere-valued lift. -/
private theorem problem_4_10_chartUnitLift_contMDiff (n : ℕ) (i : Fin (n + 1)) :
    ContMDiff (𝓡 n) (𝓡 n) ∞
      (fun x : problem_4_10_projectiveChartOpens n i ↦
        sphereToRealProjectiveSpace_chart_unit_lift n i x) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk finrank_euclideanSpace_fin
  let v : problem_4_10_projectiveChartOpens n i → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x ↦ sphereToRealProjectiveSpace_chart_lift_vector n i x
  have hv : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ v :=
    problem_4_10_chartLiftVector_contMDiff n i
  have hv_ne : ∀ x, v x ≠ 0 :=
    sphereToRealProjectiveSpace_chart_lift_vector_ne_zero n i
  have hnorm : ContMDiff (𝓡 n) (𝓘(ℝ)) ∞ (fun x ↦ ‖v x‖) := by
    intro x
    exact ((contDiffAt_norm ℝ (hv_ne x)).contMDiffAt.comp x (hv x))
  have hnormalize :
      ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (fun x ↦ ‖v x‖⁻¹ • v x) :=
    (hnorm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr (hv_ne x))).smul hv
  have hsphere :
      ContMDiff (𝓡 n) (𝓡 n) ∞
        (fun x ↦
          (⟨‖v x‖⁻¹ • v x, (sphereToRealProjectiveSpace_chart_unit_lift n i x).2⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
    hnormalize.codRestrict_sphere _
  simpa [sphereToRealProjectiveSpace_chart_unit_lift, v] using hsphere

/-- Both signed inverse branches over a standard projective chart are smooth. -/
private theorem problem_4_10_signedLift_contMDiff (n : ℕ) (i : Fin (n + 1))
    (sigma : Fin 2) :
    ContMDiff (𝓡 n) (𝓡 n) ∞
      (fun x : problem_4_10_projectiveChartOpens n i ↦
        sphereToRealProjectiveSpace_signed_lift n i sigma x) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk finrank_euclideanSpace_fin
  fin_cases sigma
  · simpa [sphereToRealProjectiveSpace_signed_lift] using
      problem_4_10_chartUnitLift_contMDiff n i
  · have hcoe :
        ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞
          (fun x : problem_4_10_projectiveChartOpens n i ↦
            ((sphereToRealProjectiveSpace_chart_unit_lift n i x :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
                EuclideanSpace ℝ (Fin (n + 1)))) := by
      exact (contMDiff_coe_sphere :
        ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞
          ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
            EuclideanSpace ℝ (Fin (n + 1)))).comp
        (problem_4_10_chartUnitLift_contMDiff n i)
    have hneg :
        ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞
          (fun x : problem_4_10_projectiveChartOpens n i ↦
            -((sphereToRealProjectiveSpace_chart_unit_lift n i x :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
                EuclideanSpace ℝ (Fin (n + 1)))) :=
      hcoe.neg
    have hsphere :
        ContMDiff (𝓡 n) (𝓡 n) ∞
          (fun x : problem_4_10_projectiveChartOpens n i ↦
            (-sphereToRealProjectiveSpace_chart_unit_lift n i x :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
      hneg.codRestrict_sphere _
    simpa [sphereToRealProjectiveSpace_signed_lift] using hsphere

/-- Totalize a signed local inverse outside its projective chart.  Its values outside the chart
are irrelevant to the partial diffeomorphism constructed below. -/
private def problem_4_10_signedLiftExtension (n : ℕ) (i : Fin (n + 1)) (sigma : Fin 2)
    (fallback : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (x : RealProjectiveSpace n) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  by
    classical
    exact if hx : x ∈ realProjectiveChartDomain n i then
      sphereToRealProjectiveSpace_signed_lift n i sigma ⟨x, hx⟩
    else fallback

/-- A positive or negative sheet over a standard projective chart is smoothly identified with
that chart by the quotient map. -/
private def problem_4_10_signedSheetPartialDiffeomorph (n : ℕ) (i : Fin (n + 1))
    (sigma : Fin 2)
    (fallback : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    PartialDiffeomorph (𝓡 n) (𝓡 n)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (RealProjectiveSpace n) ∞ where
  toPartialEquiv :=
    { toFun := sphereToRealProjectiveSpace n
      invFun := problem_4_10_signedLiftExtension n i sigma fallback
      source := sphereToRealProjectiveSpace_signed_sheet n i sigma
      target := realProjectiveChartDomain n i
      map_source' := sphereToRealProjectiveSpace_signed_sheet_subset_preimage_chartDomain n i sigma
      map_target' := by
        intro x hx
        simpa [problem_4_10_signedLiftExtension, hx] using
          sphereToRealProjectiveSpace_signed_lift_mem_sheet n i sigma ⟨x, hx⟩
      left_inv' := by
        intro y hy
        have hqy : sphereToRealProjectiveSpace n y ∈ realProjectiveChartDomain n i :=
          sphereToRealProjectiveSpace_signed_sheet_subset_preimage_chartDomain n i sigma hy
        apply sphereToRealProjectiveSpace_injOn_signed_sheet n i sigma
        · simpa [problem_4_10_signedLiftExtension, hqy] using
            sphereToRealProjectiveSpace_signed_lift_mem_sheet n i sigma ⟨_, hqy⟩
        · exact hy
        · simpa [problem_4_10_signedLiftExtension, hqy] using
            sphereToRealProjectiveSpace_signed_lift_proj n i sigma ⟨_, hqy⟩
      right_inv' := by
        intro x hx
        simpa [problem_4_10_signedLiftExtension, hx] using
          sphereToRealProjectiveSpace_signed_lift_proj n i sigma ⟨x, hx⟩ }
  open_source := sphereToRealProjectiveSpace_signed_sheet_isOpen n i sigma
  open_target := realProjectiveChartDomain_isOpen n i
  contMDiffOn_toFun := (problem_4_10_quotient_contMDiff n).contMDiffOn
  contMDiffOn_invFun := by
    intro x hx
    have hsub :
        ContMDiffAt (𝓡 n) (𝓡 n) ∞
          (fun z : problem_4_10_projectiveChartOpens n i ↦
            problem_4_10_signedLiftExtension n i sigma fallback z) ⟨x, hx⟩ := by
      simpa [problem_4_10_signedLiftExtension] using
        (problem_4_10_signedLift_contMDiff n i sigma ⟨x, hx⟩)
    exact ((contMDiffAt_subtype_iff (U := problem_4_10_projectiveChartOpens n i)
      (f := problem_4_10_signedLiftExtension n i sigma fallback) (x := ⟨x, hx⟩)).1
        hsub).contMDiffWithinAt

-- Local API note: semantic `lean_leansearch` was unavailable in this session, so this item
-- follows the established repository names `sphereToRealProjectiveSpace` and
-- `IsSmoothCoveringMap`.

/-- Problem 4-10: the quotient map `q : Sⁿ → ℝPⁿ` defined in Example 2.13(f) is a smooth covering
map. -/
theorem sphere_to_realProjectiveSpace_isSmoothCoveringMap (n : ℕ) :
    Manifold.IsSmoothCoveringMap (𝓡 n) (𝓡 n) (sphereToRealProjectiveSpace n) := by
  refine ⟨sphere_to_realProjectiveSpace_isCoveringMap n,
    sphereToRealProjectiveSpace_surjective n, ?_⟩
  intro y
  have hy_ne : ((y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0) :=
    unit_sphere_point_ne_zero n y
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1),
      ((y : EuclideanSpace ℝ (Fin (n + 1))) i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hy_ne
    ext i
    exact h i
  rcases lt_or_gt_of_ne hi with hi_neg | hi_pos
  · refine ⟨problem_4_10_signedSheetPartialDiffeomorph n i 1 y, ?_, ?_⟩
    · change y ∈ sphereToRealProjectiveSpace_signed_sheet n i 1
      simpa [sphereToRealProjectiveSpace_signed_sheet] using hi_neg
    · intro z hz
      rfl
  · refine ⟨problem_4_10_signedSheetPartialDiffeomorph n i 0 y, ?_, ?_⟩
    · change y ∈ sphereToRealProjectiveSpace_signed_sheet n i 0
      simpa [sphereToRealProjectiveSpace_signed_sheet] using hi_pos
    · intro z hz
      rfl

end


#print axioms sphere_to_realProjectiveSpace_isSmoothCoveringMap
