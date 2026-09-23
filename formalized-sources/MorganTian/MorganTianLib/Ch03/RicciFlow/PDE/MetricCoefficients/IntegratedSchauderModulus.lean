import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SchauderTimeSplit
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** integrated schauder modulus. -/
theorem integrated_schauder_modulus 
    (alpha C L T : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hT : 0 ≤ T) (F : ℝ → E3 → ℝ)
    (hF : ∀ x : E3, IntervalIntegrable (fun s => F s x) volume 0 T)
    (hmod : ∀ s ∈ Ioo (0:ℝ) T, ∀ x z : E3,
      |F s x-F s z| ≤ C*L*min (s^(alpha/2-1)) (‖x-z‖*s^(alpha/2-3/2))) :
    ∀ x z : E3, |(∫ s in (0:ℝ)..T, F s x)-(∫ s in (0:ℝ)..T, F s z)| ≤
      C*L*(2/alpha+2/(1-alpha))*‖x-z‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  intro x z
  by_cases hx : x = z
  · subst z
    simp [Real.zero_rpow (ne_of_gt ha)]
  · by_cases hT0 : T = 0
    · subst T
      simp
      positivity
    · have hTpos : 0 < T := by
        apply lt_of_le_of_ne hT
        intro h
        exact hT0 h.symm
      let rho : ℝ := ‖x - z‖
      have hrho : 0 < rho := by
        dsimp [rho]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hx)
      let w : ℝ → ℝ := fun s =>
        min (s ^ (alpha / 2 - 1)) (rho * s ^ (alpha / 2 - 3 / 2))
      obtain ⟨hwint, hwest⟩ := schauder_time_split alpha rho T ha ha1 hrho hT
      have hnotend : ∀ᵐ s ∂volume, s ≠ T := by
        exact ae_iff.mpr (by simp)
      have hpoint : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) T →
          ‖F s x - F s z‖ ≤ C * L * w s := by
        filter_upwards [hnotend] with s hsne
        intro hs
        have hslt : s < T := lt_of_le_of_ne hs.2 hsne
        rw [Real.norm_eq_abs]
        simpa [w, rho] using hmod s ⟨hs.1, hslt⟩ x z
      have hboundint : IntervalIntegrable (fun s : ℝ => C * L * w s) volume 0 T := by
        simpa [w] using hwint.const_mul (C * L)
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le hT hpoint hboundint
      have houter :
          (∫ s in (0 : ℝ)..T, F s x) - (∫ s in (0 : ℝ)..T, F s z) =
            ∫ s in (0 : ℝ)..T, (F s x - F s z) := by
        symm
        exact intervalIntegral.integral_sub (hF x) (hF z)
      have hscale :
          (∫ s in (0 : ℝ)..T, C * L * w s) =
            C * L * (∫ s in (0 : ℝ)..T, w s) := by
        rw [intervalIntegral.integral_const_mul]
      have hCL : 0 ≤ C * L := mul_nonneg hC hL
      calc
        |(∫ s in (0 : ℝ)..T, F s x) - (∫ s in (0 : ℝ)..T, F s z)| =
            ‖∫ s in (0 : ℝ)..T, (F s x - F s z)‖ := by
              rw [houter, Real.norm_eq_abs]
        _ ≤ ∫ s in (0 : ℝ)..T, C * L * w s := hnorm
        _ = C * L * (∫ s in (0 : ℝ)..T, w s) := hscale
        _ ≤ C * L * ((2 / alpha + 2 / (1 - alpha)) * rho ^ alpha) :=
          mul_le_mul_of_nonneg_left hwest hCL
        _ = C * L * (2 / alpha + 2 / (1 - alpha)) * ‖x - z‖ ^ alpha := by
          dsimp [rho]
          ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
