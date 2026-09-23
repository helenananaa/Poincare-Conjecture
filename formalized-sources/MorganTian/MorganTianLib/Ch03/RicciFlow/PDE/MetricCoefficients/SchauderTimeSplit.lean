import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** schauder time split. -/
theorem schauder_time_split 
    (alpha rho T : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) (hr : 0 < rho) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => min (t^(alpha/2-1)) (rho*t^(alpha/2-3/2))) volume 0 T ∧
      (∫ t in (0:ℝ)..T, min (t^(alpha/2-1)) (rho*t^(alpha/2-3/2))) ≤
        (2/alpha+2/(1-alpha))*rho^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  have hp : -1 < alpha / 2 - 1 := by linarith
  have hpow : IntervalIntegrable (fun t : ℝ => t ^ (alpha / 2 - 1)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hmeasPow (r : ℝ) : Measurable (fun t : ℝ => t ^ r) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const (fun _ hx => Or.inl (by simpa using hx))
  have hmeas : Measurable (fun t : ℝ =>
      min (t ^ (alpha / 2 - 1)) (rho * t ^ (alpha / 2 - 3 / 2))) := by
    exact (hmeasPow _).min ((measurable_const.mul (hmeasPow _)))
  have hbound :
      (fun t : ℝ => ‖min (t ^ (alpha / 2 - 1)) (rho * t ^ (alpha / 2 - 3 / 2))‖) ≤ᵐ[
        volume.restrict (Set.uIoc (0 : ℝ) T)] fun t => t ^ (alpha / 2 - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le hT] at ht
    have h₁ : 0 ≤ t ^ (alpha / 2 - 1) := Real.rpow_nonneg (le_of_lt ht.1) _
    have h₂ : 0 ≤ rho * t ^ (alpha / 2 - 3 / 2) :=
      mul_nonneg hr.le (Real.rpow_nonneg (le_of_lt ht.1) _)
    have hminnon : 0 ≤ min (t ^ (alpha / 2 - 1)) (rho * t ^ (alpha / 2 - 3 / 2)) :=
      le_min h₁ h₂
    rw [Real.norm_eq_abs, abs_of_nonneg hminnon]
    exact min_le_left _ _
  have hmin : IntervalIntegrable
      (fun t : ℝ => min (t ^ (alpha / 2 - 1)) (rho * t ^ (alpha / 2 - 3 / 2)))
      volume 0 T := hpow.mono_fun' hmeas.aestronglyMeasurable hbound
  have hfirst_formula (x : ℝ) :
      (∫ t in (0 : ℝ)..x, t ^ (alpha / 2 - 1)) =
        (2 / alpha) * x ^ (alpha / 2) := by
    rw [integral_rpow (a := 0) (b := x) (Or.inl hp)]
    have hzero : (0 : ℝ) ^ (alpha / 2 - 1 + 1) = 0 :=
      Real.zero_rpow (by linarith : alpha / 2 - 1 + 1 ≠ 0)
    rw [hzero, sub_zero]
    have he : alpha / 2 - 1 + 1 = alpha / 2 := by ring
    rw [he]
    have ha : alpha ≠ 0 := ne_of_gt ha
    field_simp
  have hq : alpha / 2 - 1 / 2 < 0 := by linarith
  have htail_formula (x : ℝ) (hx : rho ^ 2 ≤ x) :
      (∫ t in rho ^ 2..x, rho * t ^ (alpha / 2 - 3 / 2)) =
        rho * ((x ^ (alpha / 2 - 1 / 2) - (rho ^ 2) ^ (alpha / 2 - 1 / 2)) /
          (alpha / 2 - 1 / 2)) := by
    have hzero : (0 : ℝ) ∉ Set.uIcc (rho ^ 2) x := by
      rw [Set.uIcc_of_le hx]
      intro hz
      exact (not_le_of_gt (sq_pos_of_pos hr)) hz.1
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (a := rho ^ 2) (b := x) (Or.inr ⟨by linarith, hzero⟩)]
    have he : (alpha / 2 - 3 / 2) + 1 = alpha / 2 - 1 / 2 := by ring
    rw [he]
  have hfirst_end : (rho ^ 2) ^ (alpha / 2) = rho ^ alpha := by
    calc
      (rho ^ 2) ^ (alpha / 2) = rho ^ (2 * (alpha / 2)) :=
        (Real.rpow_natCast_mul hr.le 2 (alpha / 2)).symm
      _ = rho ^ alpha := by congr 1; ring
  have htail_end : (rho ^ 2) ^ (alpha / 2 - 1 / 2) = rho ^ (alpha - 1) := by
    calc
      (rho ^ 2) ^ (alpha / 2 - 1 / 2) = rho ^ (2 * (alpha / 2 - 1 / 2)) :=
        (Real.rpow_natCast_mul hr.le 2 (alpha / 2 - 1 / 2)).symm
      _ = rho ^ (alpha - 1) := by congr 1; ring
  have htail_bound (x : ℝ) (hx : rho ^ 2 ≤ x) :
      (∫ t in rho ^ 2..x, rho * t ^ (alpha / 2 - 3 / 2)) ≤
        (2 / (1 - alpha)) * rho ^ alpha := by
    have hformula := htail_formula x hx
    rw [hformula, htail_end]
    have hxpow : 0 ≤ x ^ (alpha / 2 - 1 / 2) :=
      Real.rpow_nonneg (le_trans (sq_nonneg rho) hx) _
    have hdiv :
        (x ^ (alpha / 2 - 1 / 2) - rho ^ (alpha - 1)) /
            (alpha / 2 - 1 / 2) ≤
          (0 - rho ^ (alpha - 1)) / (alpha / 2 - 1 / 2) := by
      rw [div_le_div_right_of_neg hq]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hdiv hr.le
    have hright : rho * ((0 - rho ^ (alpha - 1)) / (alpha / 2 - 1 / 2)) =
        (2 / (1 - alpha)) * rho ^ alpha := by
      have hprod : rho * rho ^ (alpha - 1) = rho ^ alpha := by
        calc
          rho * rho ^ (alpha - 1) = rho ^ (alpha - 1) * rho := by ring
          _ = rho ^ ((alpha - 1) + 1) :=
            (Real.rpow_add_one (ne_of_gt hr) (alpha - 1)).symm
          _ = rho ^ alpha := by congr 1; ring
      have ha1' : 1 - alpha ≠ 0 := ne_of_gt (sub_pos.mpr ha1)
      have hscalar : (0 - 1 : ℝ) / ((alpha - 1) / 2) = 2 / (1 - alpha) := by
        have haq : (alpha - 1) / 2 ≠ 0 := by linarith
        rw [div_eq_iff haq]
        field_simp [ha1']
        ring
      have hfrac : (0 - rho ^ (alpha - 1)) / (alpha / 2 - 1 / 2) =
          (2 / (1 - alpha)) * rho ^ (alpha - 1) := by
        rw [show alpha / 2 - 1 / 2 = (alpha - 1) / 2 by ring]
        calc
          (0 - rho ^ (alpha - 1)) / ((alpha - 1) / 2) =
              rho ^ (alpha - 1) * ((0 - 1 : ℝ) / ((alpha - 1) / 2)) := by ring
          _ = rho ^ (alpha - 1) * (2 / (1 - alpha)) := by rw [hscalar]
          _ = (2 / (1 - alpha)) * rho ^ (alpha - 1) := by ring
      calc
        rho * ((0 - rho ^ (alpha - 1)) / (alpha / 2 - 1 / 2)) =
            rho * ((2 / (1 - alpha)) * rho ^ (alpha - 1)) := by rw [hfrac]
        _ = (2 / (1 - alpha)) * (rho * rho ^ (alpha - 1)) := by ring
        _ = (2 / (1 - alpha)) * rho ^ alpha := by rw [hprod]
    exact hmul.trans_eq hright
  refine ⟨hmin, ?_⟩
  by_cases hsmall : T ≤ rho ^ 2
  · have hmono := intervalIntegral.integral_mono_on hT hmin hpow
        (fun _ _ => min_le_left _ _)
    rw [hfirst_formula T] at hmono
    have hpowle : T ^ (alpha / 2) ≤ rho ^ alpha := by
      calc
        T ^ (alpha / 2) ≤ (rho ^ 2) ^ (alpha / 2) :=
          Real.rpow_le_rpow hT (by nlinarith [sq_nonneg rho]) (by linarith)
        _ = rho ^ alpha := hfirst_end
    have hc : 0 ≤ 2 / alpha := by positivity
    calc
      (∫ t in (0 : ℝ)..T, min (t ^ (alpha / 2 - 1))
          (rho * t ^ (alpha / 2 - 3 / 2))) ≤ (2 / alpha) * T ^ (alpha / 2) := hmono
      _ ≤ (2 / alpha) * rho ^ alpha := mul_le_mul_of_nonneg_left hpowle hc
      _ ≤ (2 / alpha + 2 / (1 - alpha)) * rho ^ alpha := by
        have hrpow : 0 ≤ rho ^ alpha := Real.rpow_nonneg hr.le _
        have hsum : 2 / alpha ≤ 2 / alpha + 2 / (1 - alpha) :=
          le_add_of_nonneg_right (by positivity)
        exact mul_le_mul_of_nonneg_right hsum hrpow
  · have hcut : rho ^ 2 ≤ T := le_of_not_ge hsmall
    have hfirstInt : IntervalIntegrable (fun t : ℝ => t ^ (alpha / 2 - 1)) volume 0 (rho ^ 2) :=
      hpow.mono_set (by
        rw [Set.uIcc_of_le (show (0 : ℝ) ≤ rho ^ 2 by positivity), Set.uIcc_of_le hT]
        intro t ht
        exact ⟨ht.1, ht.2.trans hcut⟩)
    have hminFirst : IntervalIntegrable
        (fun t : ℝ => min (t ^ (alpha / 2 - 1)) (rho * t ^ (alpha / 2 - 3 / 2)))
        volume 0 (rho ^ 2) := hmin.mono_set (by
          rw [Set.uIcc_of_le (show (0 : ℝ) ≤ rho ^ 2 by positivity), Set.uIcc_of_le hT]
          intro t ht
          exact ⟨ht.1, ht.2.trans hcut⟩)
    have hminTail : IntervalIntegrable
        (fun t : ℝ => min (t ^ (alpha / 2 - 1)) (rho * t ^ (alpha / 2 - 3 / 2)))
        volume (rho ^ 2) T := hmin.mono_set (by
          rw [Set.uIcc_of_le hcut, Set.uIcc_of_le hT]
          intro t ht
          exact ⟨le_trans (by positivity) ht.1, ht.2⟩)
    have hsecondInt : IntervalIntegrable (fun t : ℝ => rho * t ^ (alpha / 2 - 3 / 2))
        volume (rho ^ 2) T := by
      have hzero : (0 : ℝ) ∉ Set.uIcc (rho ^ 2) T := by
        rw [Set.uIcc_of_le hcut]
        intro hz
        exact (not_le_of_gt (sq_pos_of_pos hr)) hz.1
      exact (intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)).const_mul rho
    have hfirst_le := intervalIntegral.integral_mono_on (sq_nonneg rho) hminFirst hfirstInt
      (fun _ _ => min_le_left _ _)
    have htail_le := intervalIntegral.integral_mono_on hcut hminTail hsecondInt
      (fun _ _ => min_le_right _ _)
    have hsplit := (intervalIntegral.integral_add_adjacent_intervals hminFirst hminTail).symm
    rw [hfirst_formula (rho ^ 2), hfirst_end] at hfirst_le
    have htail_final := htail_le.trans (htail_bound T hcut)
    calc
      (∫ t in (0 : ℝ)..T,
          min (t ^ (alpha / 2 - 1)) (rho * t ^ (alpha / 2 - 3 / 2))) =
          (∫ t in (0 : ℝ)..rho ^ 2,
            min (t ^ (alpha / 2 - 1)) (rho * t ^ (alpha / 2 - 3 / 2))) +
          ∫ t in rho ^ 2..T,
            min (t ^ (alpha / 2 - 1)) (rho * t ^ (alpha / 2 - 3 / 2)) := hsplit
      _ ≤ (2 / alpha) * rho ^ alpha + (2 / (1 - alpha)) * rho ^ alpha :=
        add_le_add hfirst_le htail_final
      _ = (2 / alpha + 2 / (1 - alpha)) * rho ^ alpha := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
