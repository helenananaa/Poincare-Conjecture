import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothContractionFixedPoint
open scoped ContDiff Topology NNReal
variable {P X : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
/-- Smooth dependence of the actual Banach fixed point, without assuming
smoothness of the fixed point map or invertibility of its implicit derivative. -/
theorem contDiff_fixedPoint
    (F : P × X → X) (K : ℝ≥0)
    (hF : ContDiff ℝ ∞ F)
    (hc : ∀ p : P, ContractingWith K (fun x : X => F (p, x))) :
    ContDiff ℝ ∞ (fun p : P =>
      ContractingWith.fixedPoint (fun x : X => F (p, x)) (hc p)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let R : P × X → X := fun z => z.2 - F z
  have hR : ContDiff ℝ ∞ R := by
    simpa [R] using (contDiff_snd.sub hF)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  let x : X := ContractingWith.fixedPoint (fun y : X => F (p, y)) (hc p)
  have hx : Function.IsFixedPt (fun y : X => F (p, y)) x := by
    exact ContractingWith.fixedPoint_isFixedPt (hc p)
  have hzero : R (p, x) = 0 := by
    simp only [R]
    change F (p, x) = x at hx
    rw [hx]
    simp
  let G : X → X := fun y => F (p, y)
  let D : X →L[ℝ] X := fderiv ℝ G x
  have hFdiff : DifferentiableAt ℝ F (p, x) :=
    hF.contDiffAt.differentiableAt (by simp)
  have hi : DifferentiableAt ℝ (fun y : X => (p, y)) x :=
    (differentiableAt_const p).prodMk differentiableAt_id
  have hmk : fderiv ℝ (fun y : X => (p, y)) x = ContinuousLinearMap.inr ℝ P X :=
    (hasFDerivAt_prodMk_right p x).fderiv
  have hDcomp : D = (fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P X) := by
    change fderiv ℝ (F ∘ (fun y : X => (p, y))) x = _
    rw [fderiv_comp x hFdiff hi]
    rw [hmk]
  have hDnorm : ‖D‖ ≤ (K : ℝ) := by
    simpa [D, G] using norm_fderiv_le_of_lipschitz ℝ (hc p).2
  have hK : (K : ℝ) < 1 := by exact_mod_cast (hc p).1
  have hDlt : ‖D‖ < 1 := hDnorm.trans_lt hK
  have hunit : IsUnit (1 - D) := isUnit_one_sub_of_norm_lt_one hDlt
  have hbij : Function.Bijective ⇑(1 - D) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  have hinv : (1 - D).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.ofBijective (1 - D) ?_ ?_, rfl⟩
    · exact LinearMap.ker_eq_bot.mpr hbij.1
    · exact LinearMap.range_eq_top.mpr hbij.2
  have hder : (fderiv ℝ R (p, x)).comp (ContinuousLinearMap.inr ℝ P X) =
      1 - D := by
    have hRdiff : DifferentiableAt ℝ R (p, x) :=
      hR.contDiffAt.differentiableAt (by simp)
    rw [show R = Prod.snd - F by rfl, fderiv_sub differentiableAt_snd hFdiff]
    ext y
    simp [D, hDcomp, fderiv_snd]
  have hcdf : ContDiffAt ℝ ∞ R (p, x) := hR.contDiffAt
  have hpn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let ψ := hcdf.implicitFunction hpn (by simpa [hder] using hinv)
  have hψ : ContDiffAt ℝ ∞ ψ p := hcdf.contDiffAt_implicitFunction hpn (by simpa [hder] using hinv)
  have hnear := hcdf.eventually_apply_implicitFunction hpn (by simpa [hder] using hinv)
  have heq : (fun q : P => ContractingWith.fixedPoint (fun y : X => F (q, y)) (hc q)) =ᶠ[𝓝 p] ψ := by
    filter_upwards [hnear] with q hq
    have hqzero : R (q, ψ q) = 0 := by
      simpa [hzero, R] using hq
    have hqfix : F (q, ψ q) = ψ q := by
      simp only [R] at hqzero
      exact sub_eq_zero.mp hqzero |>.symm
    have hqfixed : Function.IsFixedPt (fun y : X => F (q, y)) (ψ q) := hqfix
    exact (ContractingWith.fixedPoint_unique (hc q) hqfixed).symm
  exact hψ.congr_of_eventuallyEq heq
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothContractionFixedPoint
