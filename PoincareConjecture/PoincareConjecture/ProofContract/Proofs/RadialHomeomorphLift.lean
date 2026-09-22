import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateBallExists
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Lift a monotone real radius homeomorphism to actual Euclidean three-space. -/
theorem radial_homeomorph_lift (p : ℝ ≃ₜ ℝ) (hp : StrictMono p) (hp0 : p 0 = 0) :
    ∃ H : Euclidean3 ≃ₜ Euclidean3, H 0 = 0 ∧
      ∀ x : Euclidean3, x ≠ 0 → H x = (p ‖x‖ / ‖x‖) • x :=
/- SWARM_PROOF_BEGIN -/
by
  let Hfun : Euclidean3 → Euclidean3 := fun x =>
    if hx : x = 0 then 0 else (p ‖x‖ / ‖x‖) • x
  let Gfun : Euclidean3 → Euclidean3 := fun x =>
    if hx : x = 0 then 0 else (p.symm ‖x‖ / ‖x‖) • x
  have hp_pos : ∀ r : ℝ, 0 < r → 0 < p r := by
    intro r hr
    have h := hp hr
    simpa [hp0] using h
  have hps0 : p.symm 0 = 0 := by
    simpa [hp0] using (p.symm_apply_apply 0)
  have hps_pos : ∀ r : ℝ, 0 < r → 0 < p.symm r := by
    intro r hr
    by_contra h
    have hle : p.symm r ≤ 0 := le_of_not_gt h
    have hmap := hp.monotone hle
    rw [p.apply_symm_apply, hp0] at hmap
    linarith
  have hHnorm (x : Euclidean3) : ‖Hfun x‖ = p ‖x‖ := by
    by_cases hx : x = 0
    · simp [Hfun, hx, hp0]
    · have hxr : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hpr : 0 < p ‖x‖ := hp_pos _ hxr
      rw [show Hfun x = (p ‖x‖ / ‖x‖) • x by simp [Hfun, hx],
        norm_smul, Real.norm_of_nonneg (div_nonneg hpr.le hxr.le),
        div_mul_cancel₀ _ hxr.ne']
  have hGnorm (x : Euclidean3) : ‖Gfun x‖ = p.symm ‖x‖ := by
    by_cases hx : x = 0
    · simp [Gfun, hx, hps0]
    · have hxr : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hpr : 0 < p.symm ‖x‖ := hps_pos _ hxr
      rw [show Gfun x = (p.symm ‖x‖ / ‖x‖) • x by simp [Gfun, hx],
        norm_smul, Real.norm_of_nonneg (div_nonneg hpr.le hxr.le),
        div_mul_cancel₀ _ hxr.ne']
  have hHne (x : Euclidean3) (hx : x ≠ 0) : Hfun x ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hHnorm]
    exact (hp_pos _ (norm_pos_iff.mpr hx)).ne'
  have hGne (x : Euclidean3) (hx : x ≠ 0) : Gfun x ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hGnorm]
    exact (hps_pos _ (norm_pos_iff.mpr hx)).ne'
  have hH_at (x : Euclidean3) (hx : x ≠ 0) : ContinuousAt Hfun x := by
    have hraw : ContinuousAt (fun y : Euclidean3 =>
        (p ‖y‖ / ‖y‖) • y) x := by
      exact ((p.continuous.comp continuous_norm).continuousAt.div
        continuous_norm.continuousAt (norm_ne_zero_iff.mpr hx)).smul continuousAt_id
    have hne : {y : Euclidean3 | y ≠ 0} ∈ 𝓝 x := by
      exact isOpen_compl_singleton.mem_nhds (by simpa using hx)
    have hev : (fun y : Euclidean3 => (p ‖y‖ / ‖y‖) • y) =ᶠ[𝓝 x] Hfun := by
      filter_upwards [hne] with y hy
      simp [Hfun, hy]
    exact hraw.congr hev
  have hG_at (x : Euclidean3) (hx : x ≠ 0) : ContinuousAt Gfun x := by
    have hraw : ContinuousAt (fun y : Euclidean3 =>
        (p.symm ‖y‖ / ‖y‖) • y) x := by
      exact ((p.symm.continuous.comp continuous_norm).continuousAt.div
        continuous_norm.continuousAt (norm_ne_zero_iff.mpr hx)).smul continuousAt_id
    have hne : {y : Euclidean3 | y ≠ 0} ∈ 𝓝 x := by
      exact isOpen_compl_singleton.mem_nhds (by simpa using hx)
    have hev : (fun y : Euclidean3 => (p.symm ‖y‖ / ‖y‖) • y) =ᶠ[𝓝 x] Gfun := by
      filter_upwards [hne] with y hy
      simp [Gfun, hy]
    exact hraw.congr hev
  have hH_zero : ContinuousAt Hfun 0 := by
    have hzero : Hfun 0 = 0 := by simp [Hfun]
    rw [ContinuousAt, hzero, tendsto_zero_iff_norm_tendsto_zero]
    simpa [Function.comp_def, hHnorm, norm_zero, hp0] using
      ((p.continuous.comp continuous_norm).continuousAt.tendsto :
        Filter.Tendsto (fun x : Euclidean3 => p ‖x‖) (𝓝 0) (𝓝 (p ‖(0 : Euclidean3)‖)))
  have hG_zero : ContinuousAt Gfun 0 := by
    have hzero : Gfun 0 = 0 := by simp [Gfun]
    rw [ContinuousAt, hzero, tendsto_zero_iff_norm_tendsto_zero]
    simpa [Function.comp_def, hGnorm, norm_zero, hps0] using
      ((p.symm.continuous.comp continuous_norm).continuousAt.tendsto :
        Filter.Tendsto (fun x : Euclidean3 => p.symm ‖x‖) (𝓝 0)
          (𝓝 (p.symm ‖(0 : Euclidean3)‖)))
  have hHcont : Continuous Hfun :=
    continuous_iff_continuousAt.mpr (fun x => by
      by_cases hx : x = 0
      · simpa [hx] using hH_zero
      · exact hH_at x hx)
  have hGcont : Continuous Gfun :=
    continuous_iff_continuousAt.mpr (fun x => by
      by_cases hx : x = 0
      · simpa [hx] using hG_zero
      · exact hG_at x hx)
  have hGH : Function.LeftInverse Gfun Hfun := by
    intro x
    by_cases hx : x = 0
    · simp [Hfun, Gfun, hx]
    · have hxr : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hpr : 0 < p ‖x‖ := hp_pos _ hxr
      rw [show Gfun (Hfun x) =
          (p.symm ‖Hfun x‖ / ‖Hfun x‖) • Hfun x by
            simp [Gfun, hHne x hx], hHnorm x,
        show Hfun x = (p ‖x‖ / ‖x‖) • x by simp [Hfun, hx],
        p.symm_apply_apply, smul_smul]
      field_simp [hxr.ne', hpr.ne']
      simp
  have hHG : Function.RightInverse Gfun Hfun := by
    intro y
    by_cases hy : y = 0
    · simp [Hfun, Gfun, hy]
    · have hyr : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hpr : 0 < p.symm ‖y‖ := hps_pos _ hyr
      rw [show Hfun (Gfun y) =
          (p ‖Gfun y‖ / ‖Gfun y‖) • Gfun y by
            simp [Hfun, hGne y hy], hGnorm y,
        show Gfun y = (p.symm ‖y‖ / ‖y‖) • y by simp [Gfun, hy],
        p.apply_symm_apply, smul_smul]
      field_simp [hyr.ne', hpr.ne']
      simp
  let e : Euclidean3 ≃ₜ Euclidean3 :=
    { toEquiv :=
        { toFun := Hfun
          invFun := Gfun
          left_inv := hGH
          right_inv := hHG }
      continuous_toFun := hHcont
      continuous_invFun := hGcont }
  refine ⟨e, ?_, ?_⟩
  · simp [e, Hfun]
  · intro x hx
    simp [e, Hfun, hx]
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
