import PoincareConjecture.ParallelMath.Core

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath
open Set
open scoped Interval

/-- Scalar core of localized total-curvature smallness: the weighted time
integral with a square-root singularity is controlled by `δ` and `r`.
No cutoff, no curve-shrinking. -/
theorem localized_forcing_integral (r δ Δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (hΔb : Δ ≤ δ * r ^ 2) :
    Δ + (2 / r) * Real.sqrt Δ + Δ / r ^ 2 ≤ δ * r ^ 2 + 2 * Real.sqrt δ + δ :=
/- SWARM_PROOF_BEGIN -/
by
  have _ := hΔ
  have hsqrt : Real.sqrt Δ ≤ Real.sqrt δ * r := by
    calc
      Real.sqrt Δ ≤ Real.sqrt (δ * r ^ 2) := Real.sqrt_le_sqrt hΔb
      _ = Real.sqrt δ * Real.sqrt (r ^ 2) := Real.sqrt_mul hδ.le _
      _ = Real.sqrt δ * r := by rw [Real.sqrt_sq hr.le]
  have hmid : (2 / r) * Real.sqrt Δ ≤ 2 * Real.sqrt δ := by
    have hscale : (2 / r) * (Real.sqrt δ * r) = 2 * Real.sqrt δ := by
      rw [mul_comm (Real.sqrt δ), ← mul_assoc, div_mul_cancel₀ _ hr.ne']
    exact (mul_le_mul_of_nonneg_left hsqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr.le)).trans_eq
      hscale
  have hlast : Δ / r ^ 2 ≤ δ := (div_le_iff₀ (pow_pos hr 2)).mpr hΔb
  exact add_le_add (add_le_add hΔb hmid) hlast
/- SWARM_PROOF_END -/

theorem localized_forcing_integral_eq (r Δ : ℝ) (hr : 0 < r) (hΔ : 0 ≤ Δ) :
    (∫ s in (0 : ℝ)..Δ, (1 + 1 / (r * Real.sqrt s) + 1 / r ^ 2)) =
      Δ + (2 / r) * Real.sqrt Δ + Δ / r ^ 2 :=
/- SWARM_PROOF_BEGIN -/
by
  have _ := hr
  have hpoint : ∀ s : ℝ, 0 ≤ s →
      1 / (r * Real.sqrt s) = (1 / r) * s ^ (-(1 / 2 : ℝ)) := by
    intro s hs
    have hinv : 1 / Real.sqrt s = s ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hs]
    rw [← one_div_mul_one_div, hinv]
  have hfun :
      EqOn (fun s : ℝ => 1 + 1 / (r * Real.sqrt s) + 1 / r ^ 2)
        (fun s : ℝ => 1 + (1 / r) * s ^ (-(1 / 2 : ℝ)) + 1 / r ^ 2) [[(0 : ℝ), Δ]] := by
    intro s hs
    have hs0 : 0 ≤ s := by
      rw [uIcc_of_le hΔ] at hs
      exact hs.1
    dsimp only
    rw [hpoint s hs0]
  have hrpow : -1 < (-(1 / 2 : ℝ)) := by norm_num
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 Δ :=
    intervalIntegrable_const
  have hpow : IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume 0 Δ :=
    intervalIntegral.intervalIntegrable_rpow' hrpow
  have hmid : IntervalIntegrable (fun s : ℝ => (1 / r) * s ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume 0 Δ :=
    hpow.const_mul (1 / r)
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / r ^ 2)
      MeasureTheory.volume 0 Δ :=
    intervalIntegrable_const
  have hsum : IntervalIntegrable
      (fun s : ℝ => (1 : ℝ) + (1 / r) * s ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume 0 Δ :=
    h1.add hmid
  have hint : ∫ s in (0 : ℝ)..Δ, s ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt Δ := by
    have hI := integral_rpow (a := (0 : ℝ)) (b := Δ) (r := -(1 / 2 : ℝ)) (Or.inl hrpow)
    have hhalf : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by ring
    rw [hI, hhalf, Real.zero_rpow (by norm_num), sub_zero, ← Real.sqrt_eq_rpow]
    refine (div_eq_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)).mpr ?_
    ring
  calc
    ∫ s in (0 : ℝ)..Δ, (1 + 1 / (r * Real.sqrt s) + 1 / r ^ 2)
        = ∫ s in (0 : ℝ)..Δ,
            (1 + (1 / r) * s ^ (-(1 / 2 : ℝ)) + 1 / r ^ 2) :=
          intervalIntegral.integral_congr hfun
    _ = (∫ s in (0 : ℝ)..Δ, (1 : ℝ) + (1 / r) * s ^ (-(1 / 2 : ℝ))) +
          ∫ s in (0 : ℝ)..Δ, (1 : ℝ) / r ^ 2 :=
          intervalIntegral.integral_add hsum hconst
    _ = ((∫ _ in (0 : ℝ)..Δ, (1 : ℝ)) +
          ∫ s in (0 : ℝ)..Δ, (1 / r) * s ^ (-(1 / 2 : ℝ))) +
          ∫ s in (0 : ℝ)..Δ, (1 : ℝ) / r ^ 2 := by
          rw [intervalIntegral.integral_add h1 hmid]
    _ = ((Δ - 0) + (1 / r) * ∫ s in (0 : ℝ)..Δ, s ^ (-(1 / 2 : ℝ))) +
          (Δ - 0) * (1 / r ^ 2) := by
          simp [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
            smul_eq_mul]
    _ = Δ + (1 / r) * (2 * Real.sqrt Δ) + Δ * (1 / r ^ 2) := by
          rw [hint, sub_zero]
    _ = Δ + (2 / r) * Real.sqrt Δ + Δ / r ^ 2 := by
          ring
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath
