import PoincareConjecture.ProofContract.Refinement20260927.NormalTubeLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedTubularChartInverse
open PoincareConjecture.ProofContract.Refinement20260927
theorem tubular_chart_inverse : TubularChartInverseStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro N n X hX F hFadd hFspace hFcomplete c x endpoint project A hx hcont hderiv hproj
  letI : NormedAddCommGroup (ApproxAmbient n) :=
    PiLp.normedAddCommGroup 2 (fun _ : Fin n => ℝ)
  letI : NormedSpace ℝ (ApproxAmbient n) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin n => ℝ)
  let g : F → ApproxAmbient n := endpoint ∘ c.symm
  have hcx : c x ∈ c.target := c.map_source hx
  have hgat : ContDiffAt ℝ (↑(⊤ : ℕ∞)) g (c x) := by
    simpa [g] using hcont.contDiffAt (c.open_target.mem_nhds hcx)
  let e : OpenPartialHomeomorph F (ApproxAmbient n) :=
    hgat.toOpenPartialHomeomorph g hderiv (by norm_num)
  have hecx : c x ∈ e.source := by
    exact ContDiffAt.mem_toOpenPartialHomeomorph_source hgat hderiv (by norm_num)
  have hfdcontOn : ContinuousOn (fderiv ℝ g) c.target :=
    hcont.continuousOn_fderiv_of_isOpen c.open_target (by norm_num)
  have hfdcont : ContinuousAt (fderiv ℝ g) (c x) :=
    hfdcontOn.continuousAt (c.open_target.mem_nhds hcx)
  let T : F → F →L[ℝ] F := fun z => A.symm.toContinuousLinearMap.comp (fderiv ℝ g z)
  have hTcont : ContinuousAt T (c x) := by
    change ContinuousAt
      (fun z => A.symm.toContinuousLinearMap.comp (fderiv ℝ g z)) (c x)
    exact ((ContinuousLinearMap.compL ℝ F (ApproxAmbient n) F
      A.symm.toContinuousLinearMap).continuous.continuousAt).comp hfdcont
  have hTcx : T (c x) = ContinuousLinearMap.id ℝ F := by
    change A.symm.toContinuousLinearMap.comp (fderiv ℝ g (c x)) = _
    have hfderiv : fderiv ℝ g (c x) = A.toContinuousLinearMap := by
      change fderiv ℝ (endpoint ∘ c.symm) (c x) = A.toContinuousLinearMap
      exact hderiv.fderiv
    rw [hfderiv]
    simp
  have hTunit : IsUnit (T (c x)) := by
    rw [hTcx]
    exact isUnit_one
  have hTeventually : ∀ᶠ z in nhds (c x), IsUnit (T z) :=
    hTcont.preimage_mem_nhds (IsOpen.mem_nhds Units.isOpen hTunit)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hTeventually
  let U : Set F := (Metric.ball (c x) r ∩ c.target) ∩ e.source
  have hUopen : IsOpen U :=
    (Metric.isOpen_ball.inter c.open_target).inter e.open_source
  have hUcx : c x ∈ U := by
    exact ⟨⟨Metric.mem_ball_self hr, hcx⟩, hecx⟩
  have hUtarget : U ⊆ c.target := fun _ hz => hz.1.2
  have hUesource : U ⊆ e.source := fun _ hz => hz.2
  have hUunit : ∀ z ∈ U, IsUnit (T z) := by
    intro z hz
    exact hball (Metric.mem_ball.mp hz.1.1)
  let e₀ := e.restrOpen U hUopen
  have he₀cx : c x ∈ e₀.source := by
    change c x ∈ e.source ∩ U
    exact ⟨hecx, hUcx⟩
  have he₀symmContDiff : ContDiffOn ℝ (↑(⊤ : ℕ∞)) e₀.symm e₀.target := by
    rw [e₀.open_target.contDiffOn_iff]
    intro y hy
    let q := e₀.symm y
    have hqsrc : q ∈ e₀.source := by
      exact e₀.map_target hy
    have hqU : q ∈ U := hqsrc.2
    have hqunit : IsUnit (T q) := hUunit q hqU
    have hTbij : Function.Bijective (T q) :=
      ContinuousLinearMap.isUnit_iff_bijective.mp hqunit
    let B₀ : F ≃L[ℝ] F :=
      ContinuousLinearEquiv.ofBijective (T q)
        (LinearMap.ker_eq_bot.mpr hTbij.1)
        (LinearMap.range_eq_top.mpr hTbij.2)
    let B : F ≃L[ℝ] ApproxAmbient n := B₀.trans A
    have hqcontDiff : ContDiffAt ℝ (↑(⊤ : ℕ∞)) g q := by
      simpa [g] using hcont.contDiffAt (c.open_target.mem_nhds (hUtarget hqU))
    have hB : (B : F →L[ℝ] ApproxAmbient n) = fderiv ℝ g q := by
      apply ContinuousLinearMap.ext
      intro v
      change A (B₀ v) = fderiv ℝ g q v
      have hB₀ : B₀ v = T q v := by
        simp [B₀]
      rw [hB₀]
      simp [T]
    have hqderiv : HasFDerivAt g (B : F →L[ℝ] ApproxAmbient n) q := by
      rw [hB]
      exact (hqcontDiff.differentiableAt (by norm_num)).hasFDerivAt
    have hyE : y ∈ e.target := by
      have hEq : e q = y := by
        simpa [q, e₀] using e₀.right_inv hy
      rw [← hEq]
      exact e.map_source hqsrc.1
    have hsymmEq : e.symm y = q := by
      simp [q, e₀]
    have hqcontDiff' : ContDiffAt ℝ (↑(⊤ : ℕ∞)) g (e.symm y) := by
      simpa [hsymmEq] using hqcontDiff
    have hqderiv' : HasFDerivAt g (B : F →L[ℝ] ApproxAmbient n) (e.symm y) := by
      simpa [hsymmEq] using hqderiv
    simpa [e₀] using e.contDiffAt_symm hyE hqderiv' hqcontDiff'
  have he₀symmMDiff :
      ContMDiffOn (modelWithCornersSelf ℝ (ApproxAmbient n))
        (modelWithCornersSelf ℝ F) (↑(⊤ : ℕ∞)) e₀.symm e₀.target :=
    contMDiffOn_iff_contDiffOn.mpr he₀symmContDiff
  have hmaps : e₀.target ⊆ e₀.symm ⁻¹' c.target := by
    intro y hy
    exact hUtarget (e₀.map_target hy).2
  let d : OpenPartialHomeomorph X (ApproxAmbient n) := c.trans e₀
  have htarget : d.target = e₀.target := by
    change e₀.target ∩ e₀.symm ⁻¹' c.target = e₀.target
    exact Set.inter_eq_left.mpr hmaps
  have hcomp :
      project ∘ d.symm = (project ∘ c.symm) ∘ e₀.symm := by
    funext y
    simp [d, Function.comp_def, OpenPartialHomeomorph.coe_trans_symm]
  refine ⟨d, ?_, ?_, ?_⟩
  · change x ∈ c.source ∩ c ⁻¹' e₀.source
    exact ⟨hx, he₀cx⟩
  · intro z hz
    have hzsource : z ∈ c.source := by
      have hz' : z ∈ c.source ∩ c ⁻¹' e₀.source := by
        change z ∈ (c.trans e₀).source at hz
        simpa only [OpenPartialHomeomorph.trans_source] using hz
      exact hz'.1
    change e₀ (c z) = endpoint z
    change g (c z) = endpoint z
    simpa [g] using congrArg endpoint (c.left_inv hzsource)
  · rw [htarget, hcomp]
    exact hproj.comp he₀symmMDiff hmaps
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedTubularChartInverse
