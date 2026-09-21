import MorganTianLib.Ch02.SurgeryCap.ProfileData
import MorganTianLib.Ch02.SurgeryCap.SmoothTipCoefficients
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
import Mathlib
open Set Riemannian
open scoped ContDiff Manifold Topology RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** A global smooth radial metric with its actual polar formula and
Euclidean value at the tip. Curvature, completeness and surgery gluing remain separate. -/
theorem exists_global_round_tip_metric (P : RoundCapProfile) :
    ∃ g : RiemannianMetric (𝓡 3) E3,
      (∀ v z : E3, g.metricInner 0 v z = inner ℝ v z) ∧
      ∀ x : E3, x ≠ 0 → ∀ v z : E3,
        g.metricInner x v z =
          (P.w ‖x‖ / ‖x‖) ^ 2 * inner ℝ v z +
            ((1 - (P.w ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2) * inner ℝ x v * inner ℝ x z := by
/- SWARM_PROOF_BEGIN -/
  obtain ⟨a, b, ha, hb, ha0, hb0, hab⟩ := exists_smooth_round_tip_coefficients
  have hwle : ∀ r : ℝ, 0 < r → P.w r ≤ r := by
    intro r hr
    obtain ⟨c, hc, hder⟩ := exists_deriv_eq_slope P.w hr
      P.smooth.continuous.continuousOn
      (fun x hx => (P.smooth.differentiable (by simp) x).differentiableWithinAt)
    have hcb := P.deriv_bounds c (le_of_lt hc.1)
    rw [P.w_zero] at hder
    have hden : 0 < r - 0 := sub_pos.mpr hr
    have hder' : (P.w r - 0) / (r - 0) ≤ 1 := by
      rw [← hder]
      exact hcb.2
    have hmul : P.w r - 0 ≤ 1 * (r - 0) := (div_le_iff₀ hden).mp hder'
    linarith
  have hwpos : ∀ r : ℝ, 0 < r → 0 < P.w r := P.positive
  let A : E3 → ℝ := fun x => if x = 0 then 1 else (P.w ‖x‖ / ‖x‖) ^ 2
  let B : E3 → ℝ := fun x => if x = 0 then 1 / 12 else
    (1 - (P.w ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2
  have hApos : ∀ x : E3, 0 < A x := by
    intro x
    by_cases hx : x = 0
    · simp [A, hx]
    · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hw := hwpos ‖x‖ hnorm
      dsimp [A]
      rw [if_neg hx]
      positivity
  have hBnonneg : ∀ x : E3, 0 ≤ B x := by
    intro x
    by_cases hx : x = 0
    · simp [B, hx]
    · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hw := hwpos ‖x‖ hnorm
      have hle := hwle ‖x‖ hnorm
      have hratio' : P.w ‖x‖ / ‖x‖ ≤ 1 := (div_le_one hnorm).2 hle
      have hratio0 : 0 ≤ P.w ‖x‖ / ‖x‖ := le_of_lt (div_pos hw hnorm)
      have hratio : (P.w ‖x‖ / ‖x‖) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (P.w ‖x‖ / ‖x‖)]
      dsimp [B]
      rw [if_neg hx]
      positivity
  have hA_zero : A 0 = 1 := by simp [A]
  have hB_zero : B 0 = 1 / 12 := by simp [B]
  have hA_tip : ∀ x : E3, ‖x‖ ≤ P.r0 → A x = a (‖x‖ ^ 2) := by
    intro x hx
    by_cases hzero : x = 0
    · simp [A, hzero, ha0]
    · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hzero
      have htip := P.tip ‖x‖ (by simpa [abs_of_nonneg (norm_nonneg x)] using hx)
      have hcoeff := (hab ‖x‖).1
      dsimp [A]
      rw [if_neg hzero, htip]
      field_simp [hnorm.ne']
      nlinarith [hcoeff]
  have hB_tip : ∀ x : E3, ‖x‖ ≤ P.r0 → B x = b (‖x‖ ^ 2) := by
    intro x hx
    by_cases hzero : x = 0
    · simp [B, hzero, hb0]
    · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hzero
      have htip := P.tip ‖x‖ (by simpa [abs_of_nonneg (norm_nonneg x)] using hx)
      have hcoeff := (hab ‖x‖).2
      have hcoeffA := (hab ‖x‖).1
      dsimp [B]
      rw [if_neg hzero, htip]
      field_simp [hnorm.ne']
      nlinarith [hcoeff, hcoeffA]
  have hA_smooth : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ A := by
    intro x
    by_cases hx : x = 0
    · have hsq : ContDiffAt ℝ ∞ (fun y : E3 => ‖y‖ ^ 2) x :=
        (contDiff_norm_sq ℝ).contDiffAt
      have hlocal : ContDiffAt ℝ ∞ (fun y : E3 => a (‖y‖ ^ 2)) x :=
        ha.contDiffAt.comp x hsq
      apply contMDiffAt_iff_contDiffAt.mpr
      refine hlocal.congr_of_eventuallyEq ?_
      have hnhd : Metric.ball (0 : E3) P.r0 ∈ 𝓝 x := by
        rw [hx]
        exact Metric.ball_mem_nhds _ P.r0_pos
      filter_upwards [hnhd] with y hy
      have hy' : ‖y‖ ≤ P.r0 := le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hy)
      exact hA_tip y hy'
    · have hnorm : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
      have hnormcd : ContDiffAt ℝ ∞ (fun y : E3 => ‖y‖) x := contDiffAt_norm ℝ hx
      have hwcd : ContDiffAt ℝ ∞ (fun y : E3 => P.w ‖y‖) x :=
        P.smooth.contDiffAt.comp x hnormcd
      have hquot : ContDiffAt ℝ ∞ (fun y : E3 => P.w ‖y‖ / ‖y‖) x :=
        hwcd.div hnormcd (by simpa using hnorm)
      apply contMDiffAt_iff_contDiffAt.mpr
      refine (hquot.pow 2).congr_of_eventuallyEq ?_
      filter_upwards [eventually_ne_nhds hx] with y hy
      simp [A, hy]
  have hB_smooth : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ B := by
    intro x
    by_cases hx : x = 0
    · have hsq : ContDiffAt ℝ ∞ (fun y : E3 => ‖y‖ ^ 2) x :=
        (contDiff_norm_sq ℝ).contDiffAt
      have hlocal : ContDiffAt ℝ ∞ (fun y : E3 => b (‖y‖ ^ 2)) x :=
        hb.contDiffAt.comp x hsq
      apply contMDiffAt_iff_contDiffAt.mpr
      refine hlocal.congr_of_eventuallyEq ?_
      have hnhd : Metric.ball (0 : E3) P.r0 ∈ 𝓝 x := by
        rw [hx]
        exact Metric.ball_mem_nhds _ P.r0_pos
      filter_upwards [hnhd] with y hy
      have hy' : ‖y‖ ≤ P.r0 := le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hy)
      exact hB_tip y hy'
    · have hnorm : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
      have hnormcd : ContDiffAt ℝ ∞ (fun y : E3 => ‖y‖) x := contDiffAt_norm ℝ hx
      have hwcd : ContDiffAt ℝ ∞ (fun y : E3 => P.w ‖y‖) x :=
        P.smooth.contDiffAt.comp x hnormcd
      have hquot : ContDiffAt ℝ ∞ (fun y : E3 => P.w ‖y‖ / ‖y‖) x :=
        hwcd.div hnormcd (by simpa using hnorm)
      have hsq : ContDiffAt ℝ ∞ (fun y : E3 => ‖y‖ ^ 2) x :=
        (contDiff_norm_sq ℝ).contDiffAt
      have hnum : ContDiffAt ℝ ∞
          (fun y : E3 => 1 - (P.w ‖y‖ / ‖y‖) ^ 2) x :=
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E3 => (1 : ℝ)) x).sub (hquot.pow 2)
      have hden : ContDiffAt ℝ ∞ (fun y : E3 => ‖y‖ ^ 2) x := hsq
      apply contMDiffAt_iff_contDiffAt.mpr
      refine (hnum.div hden (by simpa using pow_ne_zero 2 hnorm)).congr_of_eventuallyEq ?_
      filter_upwards [eventually_ne_nhds hx] with y hy
      simp [B, hy]
  let φ : E3 → ℝ := fun x => ‖x‖ ^ 2 / 2
  have hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ φ := by
    have hφcd : ContDiff ℝ ∞ φ := by
      have hhalf : ContDiff ℝ ∞ (fun _ : E3 => (2 : ℝ)⁻¹) := contDiff_const
      simpa [φ, div_eq_mul_inv, smul_eq_mul] using (contDiff_norm_sq ℝ).mul hhalf
    exact hφcd.contMDiff
  let gE : RiemannianMetric (𝓡 3) E3 := DCEuclideanMetric
  let rank : ∀ x : E3, TangentSpace (𝓡 3) x →L[ℝ]
      TangentSpace (𝓡 3) x →L[ℝ] ℝ :=
    fun x => DCInducedForm (DCEuclideanMetric (F := ℝ)) φ x
  have hrank_smooth : ContMDiff (𝓡 3)
      ((𝓡 3).prod 𝓘(ℝ, (E3 →L[ℝ] E3 →L[ℝ] ℝ))) ∞
      (fun x : E3 => (⟨x, rank x⟩ :
        Bundle.TotalSpace (E3 →L[ℝ] E3 →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 3) x →L[ℝ]
            TangentSpace (𝓡 3) x →L[ℝ] ℝ))) := by
    exact DCInducedForm_contMDiff (DCEuclideanMetric (F := ℝ)) hφ
  let form : ∀ x : E3, TangentSpace (𝓡 3) x →L[ℝ]
      TangentSpace (𝓡 3) x →L[ℝ] ℝ := fun x =>
    A x • gE.inner x + B x • rank x
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E3 → Type _) :=
    ⟨gE.toRiemannianMetric⟩
  have hform_smooth : ContMDiff (𝓡 3)
      ((𝓡 3).prod 𝓘(ℝ, (E3 →L[ℝ] E3 →L[ℝ] ℝ))) ∞
      (fun x : E3 => (⟨x, form x⟩ :
        Bundle.TotalSpace (E3 →L[ℝ] E3 →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 3) x →L[ℝ]
            TangentSpace (𝓡 3) x →L[ℝ] ℝ))) := by
    exact (hA_smooth.smul_section gE.contMDiff).add_section
      (hB_smooth.smul_section hrank_smooth)
  have hrank_apply : ∀ (x v z : E3), rank x v z = inner ℝ x v * inner ℝ x z := by
    intro x v z
    rw [DCInducedForm_apply, DCEuclideanMetric_apply]
    have hderiv : fderiv ℝ φ x = innerSL ℝ x := by
      have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (1 / 2 : ℝ)
      change HasFDerivAt (fun y : E3 => (1 / 2 : ℝ) * ‖y‖ ^ 2)
        ((1 / 2 : ℝ) • 2 • innerSL ℝ x) x at h
      have hfun : (fun y : E3 => (1 / 2 : ℝ) * ‖y‖ ^ 2) = φ := by
        funext y
        dsimp [φ]
        ring
      have hf := h.fderiv
      rw [hfun] at hf
      have hs : (1 / 2 : ℝ) • 2 • (innerSL ℝ x) = innerSL ℝ x := by
        ext y
        simp [smul_eq_mul]
      rw [hs] at hf
      exact hf
    rw [mfderiv_eq_fderiv, hderiv]
    change inner ℝ x z * inner ℝ x v = inner ℝ x v * inner ℝ x z
    ring
  have hform_symm : ∀ (x : E3) (v z : TangentSpace (𝓡 3) x),
      form x v z = form x z v := by
    intro x v z
    dsimp [form]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [gE.symm x v z, hrank_apply x v z, hrank_apply x z v]
    ring
  have hform_pos : ∀ (x : E3) (v : TangentSpace (𝓡 3) x), v ≠ 0 → 0 < form x v v := by
    intro x v hv
    dsimp [form]
    have h0 : 0 < A x * gE.inner x v v :=
      mul_pos (hApos x) (gE.pos x v hv)
    have hr : 0 ≤ rank x v v := by
      rw [hrank_apply]
      nlinarith [sq_nonneg (inner ℝ x v)]
    have h1 : 0 ≤ B x * rank x v v :=
      mul_nonneg (hBnonneg x) hr
    simpa [smul_eq_mul] using add_pos_of_pos_of_nonneg h0 h1
  let g : RiemannianMetric (𝓡 3) E3 := {
    inner := form
    symm := hform_symm
    pos := hform_pos
    isVonNBounded := fun x => by
      apply isVonNBounded_of_posDef (E := E3) (form x)
      intro v hv
      exact hform_pos x v hv
    contMDiff := hform_smooth
  }
  refine ⟨g, ?_, ?_⟩
  · intro v z
    change A 0 * inner ℝ v z + B 0 * rank 0 v z = inner ℝ v z
    rw [hA_zero, hB_zero, hrank_apply]
    simp [gE, DCEuclideanMetric_apply]
  · intro x hx v z
    change A x * inner ℝ v z + B x * rank x v z = _
    rw [show A x = (P.w ‖x‖ / ‖x‖) ^ 2 by simp [A, hx],
      show B x = (1 - (P.w ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2 by simp [B, hx],
      hrank_apply]
    simp [gE, DCEuclideanMetric_apply]
    ring
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
