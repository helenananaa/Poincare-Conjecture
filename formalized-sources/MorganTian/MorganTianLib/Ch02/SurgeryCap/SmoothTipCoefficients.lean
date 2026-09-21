import Mathlib

open Set
open scoped ContDiff Topology
noncomputable section
namespace MorganTianLib.SurgeryCap

/-- **Math.** Smooth coefficients in squared radius resolve the apparent polar
singularity of the round radius-two metric at the tip. -/
theorem exists_smooth_round_tip_coefficients :
    ∃ a b : ℝ → ℝ, ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      a 0 = 1 ∧ b 0 = 1 / 12 ∧
      ∀ r : ℝ,
        r ^ 2 * a (r ^ 2) = (2 * Real.sin (r / 2)) ^ 2 ∧
        r ^ 2 * b (r ^ 2) = 1 - a (r ^ 2) := by
/- SWARM_PROOF_BEGIN -/
  let ca : ℕ → ℝ := fun n ↦
    2 * (-1 : ℝ) ^ n / (Nat.factorial (2 * n + 2) : ℝ)
  let cb : ℕ → ℝ := fun n ↦
    2 * (-1 : ℝ) ^ n / (Nat.factorial (2 * n + 4) : ℝ)
  let pa : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ ca
  let pb : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ cb
  have hca_ne : ∀ᶠ n : ℕ in Filter.atTop, ca n ≠ 0 := by
    filter_upwards [] with n
    simp [ca, Nat.factorial_ne_zero]
  have hcb_ne : ∀ᶠ n : ℕ in Filter.atTop, cb n ≠ 0 := by
    filter_upwards [] with n
    simp [cb, Nat.factorial_ne_zero]
  have hfac_a (n : ℕ) :
      Nat.factorial (2 * n + 4) =
        (2 * n + 4) * (2 * n + 3) * Nat.factorial (2 * n + 2) := by
    rw [show 2 * n + 4 = (2 * n + 3) + 1 by omega,
      show 2 * n + 3 = (2 * n + 2) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hnorm_a (m : ℕ) :
      ‖2 * (-1 : ℝ) ^ m / (Nat.factorial (2 * m + 2) : ℝ)‖ =
        2 / (Nat.factorial (2 * m + 2) : ℝ) := by
    rw [norm_div, norm_mul, norm_pow]
    norm_num
  have hca_term (n : ℕ) :
      ‖ca n.succ‖ / ‖ca n‖ =
        1 / (((2 * n + 3 : ℕ) : ℝ) * (2 * n + 4 : ℝ)) := by
    simp only [ca]
    rw [hnorm_a (n + 1), hnorm_a n]
    rw [show 2 * n.succ + 2 = 2 * n + 4 by omega, hfac_a]
    field_simp [Nat.factorial_ne_zero]
    push_cast
    ring
  have hca_ratio :
      Filter.Tendsto (fun n : ℕ ↦ ‖ca n.succ‖ / ‖ca n‖) Filter.atTop (𝓝 0) := by
    simp_rw [hca_term]
    have h₁' : Filter.Tendsto (fun n : ℕ ↦ 2 * n + 3) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop.2 fun b ↦ by
        filter_upwards [Filter.eventually_ge_atTop b] with n hn
        omega
    have h₂' : Filter.Tendsto (fun n : ℕ ↦ 2 * n + 4) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop.2 fun b ↦ by
        filter_upwards [Filter.eventually_ge_atTop b] with n hn
        omega
    have h₁ : Filter.Tendsto (fun n : ℕ ↦ ((2 * n + 3 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop.comp h₁'
    have h₂ : Filter.Tendsto (fun n : ℕ ↦ ((2 * n + 4 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop.comp h₂'
    exact (tendsto_const_nhds.div_atTop (h₁.atTop_mul_atTop₀
      (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h₂)))
  have hfac_b (n : ℕ) :
      Nat.factorial (2 * n + 6) =
        (2 * n + 6) * (2 * n + 5) * Nat.factorial (2 * n + 4) := by
    rw [show 2 * n + 6 = (2 * n + 5) + 1 by omega,
      show 2 * n + 5 = (2 * n + 4) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hnorm_b (m : ℕ) :
      ‖2 * (-1 : ℝ) ^ m / (Nat.factorial (2 * m + 4) : ℝ)‖ =
        2 / (Nat.factorial (2 * m + 4) : ℝ) := by
    rw [norm_div, norm_mul, norm_pow]
    norm_num
  have hcb_term (n : ℕ) :
      ‖cb n.succ‖ / ‖cb n‖ =
        1 / (((2 * n + 5 : ℕ) : ℝ) * (2 * n + 6 : ℝ)) := by
    simp only [cb]
    rw [hnorm_b (n + 1), hnorm_b n]
    rw [show 2 * n.succ + 4 = 2 * n + 6 by omega, hfac_b]
    field_simp [Nat.factorial_ne_zero]
    push_cast
    ring
  have hcb_ratio :
      Filter.Tendsto (fun n : ℕ ↦ ‖cb n.succ‖ / ‖cb n‖) Filter.atTop (𝓝 0) := by
    simp_rw [hcb_term]
    have h₁' : Filter.Tendsto (fun n : ℕ ↦ 2 * n + 5) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop.2 fun b ↦ by
        filter_upwards [Filter.eventually_ge_atTop b] with n hn
        omega
    have h₂' : Filter.Tendsto (fun n : ℕ ↦ 2 * n + 6) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop.2 fun b ↦ by
        filter_upwards [Filter.eventually_ge_atTop b] with n hn
        omega
    have h₁ : Filter.Tendsto (fun n : ℕ ↦ ((2 * n + 5 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop.comp h₁'
    have h₂ : Filter.Tendsto (fun n : ℕ ↦ ((2 * n + 6 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop.comp h₂'
    exact (tendsto_const_nhds.div_atTop (h₁.atTop_mul_atTop₀
      (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h₂)))
  have hpa_radius : pa.radius = ⊤ := by
    dsimp [pa]
    exact FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℝ ca hca_ne hca_ratio
  have hpb_radius : pb.radius = ⊤ := by
    dsimp [pb]
    exact FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℝ cb hcb_ne hcb_ratio
  let a : ℝ → ℝ := pa.sum
  let b : ℝ → ℝ := pb.sum
  have ha : ContDiff ℝ ∞ a := by
    dsimp [a]
    apply AnalyticOnNhd.contDiff
    simpa [hpa_radius] using
      (FormalMultilinearSeries.analyticOnNhd (p := pa))
  have hb : ContDiff ℝ ∞ b := by
    dsimp [b]
    apply AnalyticOnNhd.contDiff
    simpa [hpb_radius] using
      (FormalMultilinearSeries.analyticOnNhd (p := pb))
  have ha_zero : a 0 = 1 := by
    change FormalMultilinearSeries.ofScalarsSum ca 0 = 1
    rw [FormalMultilinearSeries.ofScalarsSum_zero]
    norm_num [ca]
  have hb_zero : b 0 = 1 / 12 := by
    change FormalMultilinearSeries.ofScalarsSum cb 0 = 1 / 12
    rw [FormalMultilinearSeries.ofScalarsSum_zero]
    norm_num [cb]
  have ha_hasSum (s : ℝ) :
      HasSum (fun n : ℕ ↦ ca n * s ^ n) (a s) := by
    have hs : s ∈ Metric.eball (0 : ℝ) pa.radius := by
      simp [hpa_radius]
    have hp := (pa.hasFPowerSeriesOnBall (by simp [hpa_radius])).hasSum hs
    simpa [a, pa, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hp
  have hb_hasSum (s : ℝ) :
      HasSum (fun n : ℕ ↦ cb n * s ^ n) (b s) := by
    have hs : s ∈ Metric.eball (0 : ℝ) pb.radius := by
      simp [hpb_radius]
    have hp := (pb.hasFPowerSeriesOnBall (by simp [hpb_radius])).hasSum hs
    simpa [b, pb, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hp
  have htail (r : ℝ) :
      HasSum
        (fun n : ℕ ↦ (-1 : ℝ) ^ (n + 1) * r ^ (2 * (n + 1)) /
          (Nat.factorial (2 * (n + 1)) : ℝ))
        (Real.cos r - 1) := by
    have h := (hasSum_nat_add_iff' 1).2 (Real.hasSum_cos r)
    simpa [Finset.sum_range_succ] using h
  have hterm_a (r : ℝ) (n : ℕ) :
      r ^ 2 * (ca n * (r ^ 2) ^ n) =
        -2 * ((-1 : ℝ) ^ (n + 1) * r ^ (2 * (n + 1)) /
          (Nat.factorial (2 * (n + 1)) : ℝ)) := by
    simp only [ca]
    rw [show 2 * (n + 1) = 2 * n + 2 by omega]
    field_simp [Nat.factorial_ne_zero]
    simp [pow_mul, pow_succ]
    ring
  have hA (r : ℝ) :
      HasSum
        (fun n : ℕ ↦ -2 * ((-1 : ℝ) ^ (n + 1) * r ^ (2 * (n + 1)) /
          (Nat.factorial (2 * (n + 1)) : ℝ)))
        (r ^ 2 * a (r ^ 2)) := by
    exact ((ha_hasSum (r ^ 2)).mul_left (r ^ 2)).congr_fun
      (fun n ↦ (hterm_a r n).symm)
  have htrig (r : ℝ) :
      -2 * (Real.cos r - 1) = (2 * Real.sin (r / 2)) ^ 2 := by
    have hc := Real.cos_two_mul_eq_one_sub (r / 2)
    rw [show 2 * (r / 2) = r by ring] at hc
    rw [hc]
    ring
  have hA_eq (r : ℝ) : r ^ 2 * a (r ^ 2) = (2 * Real.sin (r / 2)) ^ 2 := by
    rw [← htrig r]
    exact (hA r).unique ((htail r).mul_left (-2))
  have hterm_b (r : ℝ) (n : ℕ) :
      r ^ 2 * (cb n * (r ^ 2) ^ n) =
        -(ca (n + 1) * (r ^ 2) ^ (n + 1)) := by
    simp only [ca, cb]
    rw [show 2 * (n + 1) + 2 = 2 * n + 4 by omega]
    field_simp [Nat.factorial_ne_zero]
    simp [pow_succ]
    ring
  have ha_tail (r : ℝ) :
      HasSum (fun n : ℕ ↦ ca (n + 1) * (r ^ 2) ^ (n + 1))
        (a (r ^ 2) - 1) := by
    have h := (hasSum_nat_add_iff' 1).2 (ha_hasSum (r ^ 2))
    simpa [Finset.sum_range_succ, ca] using h
  have hB (r : ℝ) :
      HasSum (fun n : ℕ ↦ -(ca (n + 1) * (r ^ 2) ^ (n + 1)))
        (r ^ 2 * b (r ^ 2)) := by
    exact ((hb_hasSum (r ^ 2)).mul_left (r ^ 2)).congr_fun
      (fun n ↦ (hterm_b r n).symm)
  refine ⟨a, b, ha, hb, ha_zero, hb_zero, ?_⟩
  intro r
  refine ⟨hA_eq r, ?_⟩
  have hB_eq : r ^ 2 * b (r ^ 2) = -(a (r ^ 2) - 1) := by
    exact (hB r).unique (ha_tail r).neg
  calc
    r ^ 2 * b (r ^ 2) = -(a (r ^ 2) - 1) := hB_eq
    _ = 1 - a (r ^ 2) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
