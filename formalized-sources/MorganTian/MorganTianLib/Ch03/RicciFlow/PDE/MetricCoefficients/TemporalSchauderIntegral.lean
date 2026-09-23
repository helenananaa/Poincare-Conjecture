import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** temporal schauder integral. -/
theorem temporal_schauder_integral 
    (alpha h T : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) (hh : 0 < h) (hT : 0 ≤ T) :
    IntervalIntegrable (fun r : ℝ => min (r^(alpha/2-1)) (h*r^(alpha/2-2))) volume 0 T ∧
      (∫ r in (0:ℝ)..T, min (r^(alpha/2-1)) (h*r^(alpha/2-2))) ≤
        (2/alpha+2/(2-alpha))*h^(alpha/2) :=
/- SWARM_PROOF_BEGIN -/
by
  have hp : -1 < alpha / 2 - 1 := by linarith
  have hpow : IntervalIntegrable (fun r : ℝ => r ^ (alpha / 2 - 1)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hmeasPow (q : ℝ) : Measurable (fun r : ℝ => r ^ q) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const (fun _ hx => Or.inl (by simpa using hx))
  have hmeas : Measurable (fun r : ℝ =>
      min (r ^ (alpha / 2 - 1)) (h * r ^ (alpha / 2 - 2))) := by
    exact (hmeasPow _).min ((measurable_const.mul (hmeasPow _)))
  have hbound :
      (fun r : ℝ => ‖min (r ^ (alpha / 2 - 1)) (h * r ^ (alpha / 2 - 2))‖) ≤ᵐ[
        volume.restrict (Set.uIoc (0 : ℝ) T)] fun r => r ^ (alpha / 2 - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    rw [Set.uIoc_of_le hT] at hr
    have h₁ : 0 ≤ r ^ (alpha / 2 - 1) := Real.rpow_nonneg (le_of_lt hr.1) _
    have h₂ : 0 ≤ h * r ^ (alpha / 2 - 2) :=
      mul_nonneg hh.le (Real.rpow_nonneg (le_of_lt hr.1) _)
    have hminnon : 0 ≤ min (r ^ (alpha / 2 - 1)) (h * r ^ (alpha / 2 - 2)) :=
      le_min h₁ h₂
    rw [Real.norm_eq_abs, abs_of_nonneg hminnon]
    exact min_le_left _ _
  have hmin : IntervalIntegrable
      (fun r : ℝ => min (r ^ (alpha / 2 - 1)) (h * r ^ (alpha / 2 - 2)))
      volume 0 T := hpow.mono_fun' hmeas.aestronglyMeasurable hbound
  have hfirst_formula (x : ℝ) :
      (∫ r in (0 : ℝ)..x, r ^ (alpha / 2 - 1)) =
        (2 / alpha) * x ^ (alpha / 2) := by
    rw [integral_rpow (a := 0) (b := x) (Or.inl hp)]
    have hzero : (0 : ℝ) ^ (alpha / 2 - 1 + 1) = 0 :=
      Real.zero_rpow (by linarith : alpha / 2 - 1 + 1 ≠ 0)
    rw [hzero, sub_zero]
    have he : alpha / 2 - 1 + 1 = alpha / 2 := by ring
    rw [he]
    have ha : alpha ≠ 0 := ne_of_gt ha
    field_simp
  have hq : alpha / 2 - 1 < 0 := by linarith
  have htail_formula (x : ℝ) (hx : h ≤ x) :
      (∫ r in h..x, h * r ^ (alpha / 2 - 2)) =
        h * ((x ^ (alpha / 2 - 1) - h ^ (alpha / 2 - 1)) /
          (alpha / 2 - 1)) := by
    have hzero : (0 : ℝ) ∉ Set.uIcc h x := by
      rw [Set.uIcc_of_le hx]
      intro hz
      exact (not_le_of_gt hh) hz.1
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (a := h) (b := x) (Or.inr ⟨by linarith, hzero⟩)]
    have he : (alpha / 2 - 2) + 1 = alpha / 2 - 1 := by ring
    rw [he]
  have htail_bound (x : ℝ) (hx : h ≤ x) :
      (∫ r in h..x, h * r ^ (alpha / 2 - 2)) ≤
        (2 / (2 - alpha)) * h ^ (alpha / 2) := by
    have hformula := htail_formula x hx
    rw [hformula]
    have hxpow : 0 ≤ x ^ (alpha / 2 - 1) :=
      Real.rpow_nonneg (le_trans hh.le hx) _
    have hdiv :
        (x ^ (alpha / 2 - 1) - h ^ (alpha / 2 - 1)) /
            (alpha / 2 - 1) ≤
          (0 - h ^ (alpha / 2 - 1)) / (alpha / 2 - 1) := by
      rw [div_le_div_right_of_neg hq]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hdiv hh.le
    have hprod : h * h ^ (alpha / 2 - 1) = h ^ (alpha / 2) := by
      calc
        h * h ^ (alpha / 2 - 1) = h ^ (alpha / 2 - 1) * h := by ring
        _ = h ^ ((alpha / 2 - 1) + 1) :=
          (Real.rpow_add_one (ne_of_gt hh) (alpha / 2 - 1)).symm
        _ = h ^ (alpha / 2) := by congr 1; ring
    have hscalar : (0 - 1 : ℝ) / (alpha / 2 - 1) = 2 / (2 - alpha) := by
      have hden : alpha / 2 - 1 ≠ 0 := by linarith
      have hden' : 2 - alpha ≠ 0 := by linarith
      rw [div_eq_iff hden]
      field_simp [hden']
      ring
    have hfrac :
        (0 - h ^ (alpha / 2 - 1)) / (alpha / 2 - 1) =
          (2 / (2 - alpha)) * h ^ (alpha / 2 - 1) := by
      calc
        (0 - h ^ (alpha / 2 - 1)) / (alpha / 2 - 1) =
            h ^ (alpha / 2 - 1) * ((0 - 1 : ℝ) / (alpha / 2 - 1)) := by ring
        _ = h ^ (alpha / 2 - 1) * (2 / (2 - alpha)) := by rw [hscalar]
        _ = (2 / (2 - alpha)) * h ^ (alpha / 2 - 1) := by ring
    have hright :
        h * ((0 - h ^ (alpha / 2 - 1)) / (alpha / 2 - 1)) =
          (2 / (2 - alpha)) * h ^ (alpha / 2) := by
      calc
        h * ((0 - h ^ (alpha / 2 - 1)) / (alpha / 2 - 1)) =
            h * ((2 / (2 - alpha)) * h ^ (alpha / 2 - 1)) := by rw [hfrac]
        _ = (2 / (2 - alpha)) * (h * h ^ (alpha / 2 - 1)) := by ring
        _ = (2 / (2 - alpha)) * h ^ (alpha / 2) := by rw [hprod]
    calc
      h * ((x ^ (alpha / 2 - 1) - h ^ (alpha / 2 - 1)) /
          (alpha / 2 - 1)) ≤
          h * ((0 - h ^ (alpha / 2 - 1)) / (alpha / 2 - 1)) := hmul
      _ = (2 / (2 - alpha)) * h ^ (alpha / 2) := hright
  refine ⟨hmin, ?_⟩
  by_cases hsmall : T ≤ h
  · have hmono := intervalIntegral.integral_mono_on hT hmin hpow
        (fun _ _ => min_le_left _ _)
    rw [hfirst_formula T] at hmono
    have hpowle : T ^ (alpha / 2) ≤ h ^ (alpha / 2) := by
      exact Real.rpow_le_rpow hT hsmall (by linarith)
    have hc : 0 ≤ 2 / alpha := by positivity
    calc
      (∫ r in (0 : ℝ)..T, min (r ^ (alpha / 2 - 1)) (h * r ^ (alpha / 2 - 2)))
          ≤ (2 / alpha) * T ^ (alpha / 2) := hmono
      _ ≤ (2 / alpha) * h ^ (alpha / 2) := mul_le_mul_of_nonneg_left hpowle hc
      _ ≤ (2 / alpha + 2 / (2 - alpha)) * h ^ (alpha / 2) := by
        have hhp : 0 ≤ h ^ (alpha / 2) := Real.rpow_nonneg hh.le _
        have hden : 0 < 2 - alpha := by linarith
        have hsum : 2 / alpha ≤ 2 / alpha + 2 / (2 - alpha) :=
          le_add_of_nonneg_right (by positivity)
        exact mul_le_mul_of_nonneg_right hsum hhp
  · have hcut : h ≤ T := le_of_not_ge hsmall
    have hfirstInt : IntervalIntegrable (fun r : ℝ => r ^ (alpha / 2 - 1)) volume 0 h :=
      hpow.mono_set (by
        rw [Set.uIcc_of_le hh.le, Set.uIcc_of_le hT]
        intro r hr
        exact ⟨hr.1, hr.2.trans hcut⟩)
    have hminFirst : IntervalIntegrable
        (fun r : ℝ => min (r ^ (alpha / 2 - 1)) (h * r ^ (alpha / 2 - 2)))
        volume 0 h := hmin.mono_set (by
          rw [Set.uIcc_of_le hh.le, Set.uIcc_of_le hT]
          intro r hr
          exact ⟨hr.1, hr.2.trans hcut⟩)
    have hminTail : IntervalIntegrable
        (fun r : ℝ => min (r ^ (alpha / 2 - 1)) (h * r ^ (alpha / 2 - 2)))
        volume h T := hmin.mono_set (by
          rw [Set.uIcc_of_le hcut, Set.uIcc_of_le hT]
          intro r hr
          exact ⟨le_trans hh.le hr.1, hr.2⟩)
    have hsecondInt : IntervalIntegrable (fun r : ℝ => h * r ^ (alpha / 2 - 2))
        volume h T := by
      have hzero : (0 : ℝ) ∉ Set.uIcc h T := by
        rw [Set.uIcc_of_le hcut]
        intro hz
        exact (not_le_of_gt hh) hz.1
      exact (intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)).const_mul h
    have hfirst_le := intervalIntegral.integral_mono_on hh.le hminFirst hfirstInt
      (fun _ _ => min_le_left _ _)
    have htail_le := intervalIntegral.integral_mono_on hcut hminTail hsecondInt
      (fun _ _ => min_le_right _ _)
    have hsplit := (intervalIntegral.integral_add_adjacent_intervals hminFirst hminTail).symm
    rw [hfirst_formula h] at hfirst_le
    have htail_final := htail_le.trans (htail_bound T hcut)
    calc
      (∫ r in (0 : ℝ)..T,
          min (r ^ (alpha / 2 - 1)) (h * r ^ (alpha / 2 - 2))) =
          (∫ r in (0 : ℝ)..h,
            min (r ^ (alpha / 2 - 1)) (h * r ^ (alpha / 2 - 2))) +
          ∫ r in h..T, min (r ^ (alpha / 2 - 1)) (h * r ^ (alpha / 2 - 2)) := hsplit
      _ ≤ (2 / alpha) * h ^ (alpha / 2) + (2 / (2 - alpha)) * h ^ (alpha / 2) :=
        add_le_add hfirst_le htail_final
      _ = (2 / alpha + 2 / (2 - alpha)) * h ^ (alpha / 2) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
