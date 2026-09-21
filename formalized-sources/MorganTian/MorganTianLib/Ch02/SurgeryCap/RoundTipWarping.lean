import Mathlib
open Set
open scoped ContDiff
noncomputable section
namespace MorganTianLib.SurgeryCap

/-- **Math.** A constructed concave radial profile, spherical at the tip and cylindrical at infinity.
This is scalar data for a cap metric; curvature, completeness and gluing are separate obligations. -/
theorem exists_round_tip_cylindrical_warping :
    ∃ (r0 A : ℝ) (w : ℝ → ℝ), 0 < r0 ∧ r0 < A ∧ ContDiff ℝ ∞ w ∧
      (∀ r, |r| ≤ r0 → w r = 2 * Real.sin (r / 2)) ∧
      (∀ r, A ≤ r → w r = Real.sqrt 2) ∧
      (∀ r, 0 < r → 0 < w r) ∧
      (∀ r, 0 ≤ r → deriv w r ∈ Icc (0 : ℝ) 1) ∧
      (∀ r, 0 < r → deriv w r < 1) ∧
      (∀ r, 0 ≤ r → deriv (deriv w) r ≤ 0) := by
/- SWARM_PROOF_BEGIN -/
  let base : ℝ → ℝ := fun x =>
    Real.sin (x / 2) / 2 * (1 - Real.smoothTransition (32 * x - 1))
  let bump₁ : ℝ → ℝ := fun x =>
    Real.smoothTransition (4 * x - 2) * (1 - Real.smoothTransition (4 * x - 3))
  let bump₂ : ℝ → ℝ := fun x =>
    Real.smoothTransition (4 * x - 8) * (1 - Real.smoothTransition (4 * x - 9))
  have hbase_smooth : ContDiff ℝ ∞ base := by
    dsimp [base]
    fun_prop
  have hbump₁_smooth : ContDiff ℝ ∞ bump₁ := by
    dsimp [bump₁]
    fun_prop
  have hbump₂_smooth : ContDiff ℝ ∞ bump₂ := by
    dsimp [bump₂]
    fun_prop
  have hbase_zero : ∀ x, (1 / 16 : ℝ) ≤ x → base x = 0 := by
    intro x hx
    dsimp [base]
    have harg : (1 : ℝ) ≤ 32 * x - 1 := by linarith
    rw [Real.smoothTransition.one_of_one_le harg]
    ring
  have hbump₁_zero_left : ∀ x, x ≤ (1 / 2 : ℝ) → bump₁ x = 0 := by
    intro x hx
    dsimp [bump₁]
    have harg : 4 * x - 2 ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos harg]
    ring
  have hbump₁_zero_right : ∀ x, 1 ≤ x → bump₁ x = 0 := by
    intro x hx
    dsimp [bump₁]
    have harg : (1 : ℝ) ≤ 4 * x - 3 := by linarith
    rw [Real.smoothTransition.one_of_one_le harg]
    ring
  have hbump₂_zero_left : ∀ x, x ≤ (2 : ℝ) → bump₂ x = 0 := by
    intro x hx
    dsimp [bump₂]
    have harg : 4 * x - 8 ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos harg]
    ring
  have hbump₂_zero_right : ∀ x, (5 / 2 : ℝ) ≤ x → bump₂ x = 0 := by
    intro x hx
    dsimp [bump₂]
    have harg : (1 : ℝ) ≤ 4 * x - 9 := by linarith
    rw [Real.smoothTransition.one_of_one_le harg]
    ring
  have hbase_nonneg : ∀ x, 0 ≤ x → 0 ≤ base x := by
    intro x hx
    by_cases hxs : x ≤ (1 / 16 : ℝ)
    · dsimp [base]
      have hs : 0 ≤ Real.sin (x / 2) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · positivity
        · nlinarith [Real.pi_gt_three]
      have hp : 0 ≤ 1 - Real.smoothTransition (32 * x - 1) :=
        sub_nonneg.mpr (Real.smoothTransition.le_one _)
      exact mul_nonneg (div_nonneg hs (by norm_num)) hp
    · exact (hbase_zero x (le_of_not_ge hxs)).ge
  have hbase_upper : ∀ x, 0 ≤ x → base x ≤ (1 / 2 : ℝ) := by
    intro x hx
    by_cases hxs : x ≤ (1 / 16 : ℝ)
    · dsimp [base]
      have hs0 : 0 ≤ Real.sin (x / 2) / 2 := by
        have hs : 0 ≤ Real.sin (x / 2) := by
          apply Real.sin_nonneg_of_nonneg_of_le_pi
          · positivity
          · nlinarith [Real.pi_gt_three]
        positivity
      have hs1 : Real.sin (x / 2) / 2 ≤ (1 / 2 : ℝ) := by
        have := Real.sin_le_one (x / 2)
        nlinarith
      have hp0 : 0 ≤ 1 - Real.smoothTransition (32 * x - 1) :=
        sub_nonneg.mpr (Real.smoothTransition.le_one _)
      have hp1 : 1 - Real.smoothTransition (32 * x - 1) ≤ 1 := by
        linarith [Real.smoothTransition.nonneg (32 * x - 1)]
      calc
        Real.sin (x / 2) / 2 * (1 - Real.smoothTransition (32 * x - 1))
            ≤ (Real.sin (x / 2) / 2) * 1 := by
              exact mul_le_mul_of_nonneg_left hp1 hs0
        _ ≤ (1 / 2 : ℝ) := by simpa using hs1
    · rw [hbase_zero x (le_of_not_ge hxs)]
      norm_num
  have hbump₁_nonneg : ∀ x, 0 ≤ bump₁ x := by
    intro x
    dsimp [bump₁]
    exact mul_nonneg (Real.smoothTransition.nonneg _) <|
      sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hbump₂_nonneg : ∀ x, 0 ≤ bump₂ x := by
    intro x
    dsimp [bump₂]
    exact mul_nonneg (Real.smoothTransition.nonneg _) <|
      sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hbump₁_pos : 0 < bump₁ (5 / 8 : ℝ) := by
    dsimp [bump₁]
    have h₁ : 0 < Real.smoothTransition ((1 : ℝ) / 2) := by
      apply Real.smoothTransition.pos_of_pos
      norm_num
    have h₂ : Real.smoothTransition (-(1 / 2 : ℝ)) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      norm_num
    norm_num
    rw [h₂]
    nlinarith [h₁]
  have hbump₂_pos : 0 < bump₂ (9 / 4 : ℝ) := by
    dsimp [bump₂]
    have h₁ : Real.smoothTransition (1 : ℝ) = 1 :=
      Real.smoothTransition.one_of_one_le le_rfl
    have h₂ : Real.smoothTransition (0 : ℝ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by norm_num)
    norm_num [h₁, h₂]
  have hbump₁_cont : Continuous bump₁ := hbump₁_smooth.continuous
  have hbump₂_cont : Continuous bump₂ := hbump₂_smooth.continuous
  have hbase_cont : Continuous base := hbase_smooth.continuous
  let m₀ : ℝ := ∫ x in (0 : ℝ)..3, base x
  let m₁ : ℝ := ∫ x in (0 : ℝ)..3, x * base x
  let b₁₀ : ℝ := ∫ x in (0 : ℝ)..3, bump₁ x
  let b₁₁ : ℝ := ∫ x in (0 : ℝ)..3, x * bump₁ x
  let b₂₀ : ℝ := ∫ x in (0 : ℝ)..3, bump₂ x
  let b₂₁ : ℝ := ∫ x in (0 : ℝ)..3, x * bump₂ x
  have hbase_int : IntervalIntegrable base MeasureTheory.volume 0 3 :=
    hbase_cont.intervalIntegrable _ _
  have hbump₁_int : IntervalIntegrable bump₁ MeasureTheory.volume 0 3 :=
    hbump₁_cont.intervalIntegrable _ _
  have hbump₂_int : IntervalIntegrable bump₂ MeasureTheory.volume 0 3 :=
    hbump₂_cont.intervalIntegrable _ _
  have hxb_int : IntervalIntegrable (fun x => x * base x) MeasureTheory.volume 0 3 := by
    exact (continuous_id.mul hbase_cont).intervalIntegrable _ _
  have hxb₁_int : IntervalIntegrable (fun x => x * bump₁ x) MeasureTheory.volume 0 3 := by
    exact (continuous_id.mul hbump₁_cont).intervalIntegrable _ _
  have hxb₂_int : IntervalIntegrable (fun x => x * bump₂ x) MeasureTheory.volume 0 3 := by
    exact (continuous_id.mul hbump₂_cont).intervalIntegrable _ _
  have hm₀_nonneg : 0 ≤ m₀ := by
    dsimp [m₀]
    apply intervalIntegral.integral_nonneg zero_le_three
    intro x hx
    exact hbase_nonneg x hx.1
  have hbase_small : m₀ ≤ (1 / 32 : ℝ) := by
    have hfirst : ∫ x in (0 : ℝ)..(1 / 16 : ℝ), base x ≤
        ∫ x in (0 : ℝ)..(1 / 16 : ℝ), (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact hbase_cont.intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro x hx
        exact hbase_upper x hx.1
    have hsecond : (∫ x in (1 / 16 : ℝ)..3, base x) = 0 := by
      rw [← intervalIntegral.integral_zero]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (1 / 16 : ℝ) ≤ 3)] at hx
      simp [hbase_zero x hx.1]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hbase_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 (1 / 16))
      (hbase_cont.intervalIntegrable (μ := MeasureTheory.volume) (1 / 16) 3)
    dsimp [m₀]
    rw [← hadd, hsecond]
    norm_num [intervalIntegral.integral_const] at hfirst ⊢
    exact hfirst
  have hm₁_nonneg : 0 ≤ m₁ := by
    dsimp [m₁]
    apply intervalIntegral.integral_nonneg zero_le_three
    intro x hx
    exact mul_nonneg hx.1 (hbase_nonneg x hx.1)
  have hm₁_bound : m₁ ≤ (1 / 16 : ℝ) * m₀ := by
    have hmono : ∫ x in (0 : ℝ)..3, x * base x ≤
        ∫ x in (0 : ℝ)..3, (1 / 16 : ℝ) * base x := by
      apply intervalIntegral.integral_mono_on zero_le_three hxb_int
        (hbase_int.const_mul (1 / 16 : ℝ))
      intro x hx
      by_cases hsmall : x ≤ (1 / 16 : ℝ)
      · nlinarith [hbase_nonneg x hx.1]
      · rw [hbase_zero x (le_of_not_ge hsmall)]
        simp
    dsimp [m₁, m₀] at *
    simpa [intervalIntegral.integral_const_mul] using hmono
  have hb₁₀_pos : 0 < b₁₀ := by
    dsimp [b₁₀]
    apply intervalIntegral.integral_pos (by norm_num) hbump₁_cont.continuousOn
    · intro x hx
      exact hbump₁_nonneg x
    · refine ⟨5 / 8, by constructor <;> norm_num, hbump₁_pos⟩
  have hb₂₀_pos : 0 < b₂₀ := by
    dsimp [b₂₀]
    apply intervalIntegral.integral_pos (by norm_num) hbump₂_cont.continuousOn
    · intro x hx
      exact hbump₂_nonneg x
    · refine ⟨9 / 4, by constructor <;> norm_num, hbump₂_pos⟩
  have hb₁₁_le : b₁₁ ≤ b₁₀ := by
    have hmono : ∫ x in (0 : ℝ)..3, x * bump₁ x ≤
        ∫ x in (0 : ℝ)..3, bump₁ x := by
      apply intervalIntegral.integral_mono_on zero_le_three hxb₁_int hbump₁_int
      intro x hx
      by_cases hsmall : x ≤ (1 : ℝ)
      · exact mul_le_of_le_one_left (hbump₁_nonneg x) (by linarith [hx.1])
      · rw [hbump₁_zero_right x (le_of_not_ge hsmall)]
        simp
    exact hmono
  have hb₂₁_strict : 2 * b₂₀ < b₂₁ := by
    have hpos : 0 < ∫ x in (0 : ℝ)..3, (x - 2) * bump₂ x := by
      have hcont : Continuous (fun x : ℝ => (x - 2) * bump₂ x) :=
        (continuous_id.sub continuous_const).mul hbump₂_cont
      apply intervalIntegral.integral_pos (a := (0 : ℝ)) (b := 3) (by norm_num)
        hcont.continuousOn
      · intro x hx
        by_cases hsmall : x ≤ (2 : ℝ)
        · rw [hbump₂_zero_left x hsmall]
          simp [hsmall]
        · exact mul_nonneg (by linarith) (hbump₂_nonneg x)
      · refine ⟨9 / 4, by constructor <;> norm_num, ?_⟩
        norm_num [hbump₂_pos]
    have heq : ∫ x in (0 : ℝ)..3, (x - 2) * bump₂ x = b₂₁ - 2 * b₂₀ := by
      rw [show (fun x => (x - 2) * bump₂ x) =
          (fun x => x * bump₂ x - 2 * bump₂ x) by funext x <;> ring]
      rw [intervalIntegral.integral_sub hxb₂_int (hbump₂_int.const_mul 2)]
      simp only [b₂₁, b₂₀, intervalIntegral.integral_const_mul]
    rw [heq] at hpos
    nlinarith [hpos]
  have hm₀_le : m₀ ≤ (1 / 32 : ℝ) := hbase_small
  have hM_pos : 0 < 1 - m₀ := by linarith
  have hm₁_small : m₁ ≤ (1 / 512 : ℝ) := by
    calc
      m₁ ≤ (1 / 16 : ℝ) * m₀ := hm₁_bound
      _ ≤ (1 / 16 : ℝ) * (1 / 32 : ℝ) :=
        mul_le_mul_of_nonneg_left hm₀_le (by norm_num)
      _ = (1 / 512 : ℝ) := by norm_num
  have hQ_pos : 0 < Real.sqrt 2 - m₁ := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrt1 : 1 < Real.sqrt 2 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
    linarith
  have hQ_gt_M : 1 - m₀ < Real.sqrt 2 - m₁ := by
    have hsqrt : 1 < Real.sqrt 2 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
    nlinarith [hm₁_bound, hm₁_nonneg]
  have hQ_lt_twoM : Real.sqrt 2 - m₁ < 2 * (1 - m₀) := by
    have hsqrt : Real.sqrt 2 < (3 / 2 : ℝ) := by
      apply (Real.sqrt_lt' (by norm_num)).2
      norm_num
    nlinarith [hm₀_le, hm₁_nonneg]
  have hb₂₁_pos : 0 < b₂₁ := by
    nlinarith [hb₂₁_strict, hb₂₀_pos]
  let D : ℝ := b₁₀ * b₂₁ - b₁₁ * b₂₀
  have hD_pos : 0 < D := by
    dsimp [D]
    have hp₁ : 2 * b₁₀ * b₂₀ < b₁₀ * b₂₁ := by
      nlinarith [mul_lt_mul_of_pos_left hb₂₁_strict hb₁₀_pos]
    have hp₂ : b₁₁ * b₂₀ ≤ b₁₀ * b₂₀ := by
      exact mul_le_mul_of_nonneg_right hb₁₁_le hb₂₀_pos.le
    nlinarith
  let α : ℝ := ((1 - m₀) * b₂₁ - (Real.sqrt 2 - m₁) * b₂₀) / D
  let β : ℝ := ((Real.sqrt 2 - m₁) * b₁₀ - (1 - m₀) * b₁₁) / D
  have hα_pos : 0 < α := by
    dsimp [α]
    apply div_pos
    · have hp₁ : (Real.sqrt 2 - m₁) * b₂₀ <
          2 * (1 - m₀) * b₂₀ :=
        mul_lt_mul_of_pos_right hQ_lt_twoM hb₂₀_pos
      have hp₂ : 2 * (1 - m₀) * b₂₀ < (1 - m₀) * b₂₁ := by
        nlinarith [mul_lt_mul_of_pos_left hb₂₁_strict hM_pos]
      nlinarith
    · exact hD_pos
  have hβ_pos : 0 < β := by
    dsimp [β]
    apply div_pos
    · have hp₁ : (1 - m₀) * b₁₁ ≤ (1 - m₀) * b₁₀ :=
        mul_le_mul_of_nonneg_left hb₁₁_le hM_pos.le
      have hp₂ : (1 - m₀) * b₁₀ < (Real.sqrt 2 - m₁) * b₁₀ :=
        mul_lt_mul_of_pos_right hQ_gt_M hb₁₀_pos
      nlinarith
    · exact hD_pos
  have hmass : m₀ + α * b₁₀ + β * b₂₀ = 1 := by
    dsimp [α, β, D]
    have hden : b₂₁ * b₁₀ - b₂₀ * b₁₁ ≠ 0 := by
      nlinarith [hD_pos]
    field_simp [hden]
    ring
  have hmoment : m₁ + α * b₁₁ + β * b₂₁ = Real.sqrt 2 := by
    dsimp [α, β, D]
    have hden : b₂₁ * b₁₀ - b₂₀ * b₁₁ ≠ 0 := by
      nlinarith [hD_pos]
    field_simp [hden]
    ring
  let k : ℝ → ℝ := fun x => base x + α * bump₁ x + β * bump₂ x
  have hk_smooth : ContDiff ℝ ∞ k := by
    dsimp [k]
    fun_prop
  have hk_cont : Continuous k := hk_smooth.continuous
  have hk_nonneg : ∀ x, 0 ≤ x → 0 ≤ k x := by
    intro x hx
    dsimp [k]
    exact add_nonneg
      (add_nonneg (hbase_nonneg x hx) (mul_nonneg hα_pos.le (hbump₁_nonneg x)))
      (mul_nonneg hβ_pos.le (hbump₂_nonneg x))
  have hk_tip : ∀ x, x ≤ (1 / 32 : ℝ) → k x = Real.sin (x / 2) / 2 := by
    intro x hx
    dsimp [k, base]
    have hp : Real.smoothTransition (32 * x - 1) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      linarith
    have h₁ : bump₁ x = 0 := hbump₁_zero_left x (by linarith)
    have h₂ : bump₂ x = 0 := hbump₂_zero_left x (by linarith)
    rw [hp, h₁, h₂]
    ring
  have hk_zero : ∀ x, 3 ≤ x → k x = 0 := by
    intro x hx
    dsimp [k]
    rw [hbase_zero x (by linarith), hbump₁_zero_right x (by linarith),
      hbump₂_zero_right x (by linarith)]
    ring
  have hk_int : IntervalIntegrable k MeasureTheory.volume 0 3 :=
    hk_cont.intervalIntegrable _ _
  have hxk_int : IntervalIntegrable (fun x => x * k x) MeasureTheory.volume 0 3 := by
    exact (continuous_id.mul hk_cont).intervalIntegrable _ _
  have hkmass : (∫ x in (0 : ℝ)..3, k x) = 1 := by
    calc
      (∫ x in (0 : ℝ)..3, k x) =
          (∫ x in (0 : ℝ)..3, base x) +
            (∫ x in (0 : ℝ)..3, α * bump₁ x) +
              (∫ x in (0 : ℝ)..3, β * bump₂ x) := by
        dsimp [k]
        rw [intervalIntegral.integral_add
          (hbase_int.add (hbump₁_int.const_mul α)) (hbump₂_int.const_mul β)]
        rw [intervalIntegral.integral_add hbase_int (hbump₁_int.const_mul α)]
      _ = m₀ + α * b₁₀ + β * b₂₀ := by
        simp only [m₀, b₁₀, b₂₀, intervalIntegral.integral_const_mul]
      _ = 1 := hmass
  have hkmoment : (∫ x in (0 : ℝ)..3, x * k x) = Real.sqrt 2 := by
    calc
      (∫ x in (0 : ℝ)..3, x * k x) =
      (∫ x in (0 : ℝ)..3, x * base x) +
            (∫ x in (0 : ℝ)..3, α * (x * bump₁ x)) +
              (∫ x in (0 : ℝ)..3, β * (x * bump₂ x)) := by
        change (∫ x in (0 : ℝ)..3, x *
          (base x + α * bump₁ x + β * bump₂ x)) = _
        rw [show (fun x : ℝ => x * (base x + α * bump₁ x + β * bump₂ x)) =
            (fun x => x * base x + α * (x * bump₁ x) + β * (x * bump₂ x)) by
              funext x <;> ring]
        rw [intervalIntegral.integral_add
          (hxb_int.add (hxb₁_int.const_mul α)) (hxb₂_int.const_mul β)]
        rw [intervalIntegral.integral_add hxb_int (hxb₁_int.const_mul α)]
      _ = m₁ + α * b₁₁ + β * b₂₁ := by
        simp only [m₁, b₁₁, b₂₁, intervalIntegral.integral_const_mul]
      _ = Real.sqrt 2 := hmoment
  let F : ℝ → ℝ := fun r => ∫ x in (0 : ℝ)..r, k x
  let G : ℝ → ℝ := fun r => ∫ x in (0 : ℝ)..r, x * k x
  have hF_diff : Differentiable ℝ F := by
    dsimp [F]
    exact intervalIntegral.differentiable_integral_of_continuous hk_cont
  have hxk_cont : Continuous (fun x => x * k x) := continuous_id.mul hk_cont
  have hG_diff : Differentiable ℝ G := by
    dsimp [G]
    exact intervalIntegral.differentiable_integral_of_continuous hxk_cont
  have hF_has : ∀ r, HasDerivAt F (k r) r := by
    intro r
    dsimp [F]
    exact intervalIntegral.integral_hasDerivAt_right
      (hk_cont.intervalIntegrable _ _) hk_cont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hk_cont.continuousAt
  have hG_has : ∀ r, HasDerivAt G (r * k r) r := by
    intro r
    dsimp [G]
    simpa using (intervalIntegral.integral_hasDerivAt_right
      (hxk_cont.intervalIntegrable _ _)
      hxk_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hxk_cont.continuousAt)
  have hF_deriv : deriv F = k := by
    funext r
    exact (hF_has r).deriv
  have hG_deriv : deriv G = fun r => r * k r := by
    funext r
    exact (hG_has r).deriv
  have hF_smooth : ContDiff ℝ ∞ F := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hF_diff, hF_deriv ▸ hk_smooth⟩
  have hG_smooth : ContDiff ℝ ∞ G := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hG_diff, hG_deriv ▸ (contDiff_id.mul hk_smooth)⟩
  let w : ℝ → ℝ := fun r => r * (1 - F r) + G r
  have hw_smooth : ContDiff ℝ ∞ w := by
    simpa [w] using
      ((contDiff_id.mul (contDiff_const.sub hF_smooth)).add hG_smooth)
  have hw_has : ∀ r, HasDerivAt w (1 - F r) r := by
    intro r
    have h := ((hasDerivAt_id r).mul ((hasDerivAt_const r (1 : ℝ)).sub (hF_has r))).add
      (hG_has r)
    change HasDerivAt (fun x : ℝ => x * (1 - F x) + G x) (1 - F r) r
    have hd : (1 * (1 - F r) + r * (0 - k r) + r * k r) = 1 - F r := by
      ring
    have h' : HasDerivAt (id * ((fun x : ℝ => 1) - F) + G) (1 - F r) r := hd ▸ h
    apply h'.congr_of_eventuallyEq
    filter_upwards [] with x
    dsimp <;> ring
  have hw_deriv : ∀ r, deriv w r = 1 - F r := by
    intro r
    exact (hw_has r).deriv
  have hw_second : ∀ r, deriv (deriv w) r = -k r := by
    have hwd : deriv w = fun r => 1 - F r := funext hw_deriv
    intro r
    rw [hwd]
    change deriv (fun x : ℝ => 1 - F x) r = -k r
    have h' := (hasDerivAt_const r (1 : ℝ)).sub (hF_has r)
    have h : HasDerivAt (fun x : ℝ => 1 - F x) (0 - k r) r := by
      apply h'.congr_of_eventuallyEq
      filter_upwards [] with x
      rfl
    simpa only [zero_sub] using h.deriv
  have hF_nonneg : ∀ r, 0 ≤ r → 0 ≤ F r := by
    intro r hr
    dsimp [F]
    apply intervalIntegral.integral_nonneg hr
    intro x hx
    exact hk_nonneg x hx.1
  have htail_k_zero : ∀ r, 3 ≤ r → (∫ x in (3 : ℝ)..r, k x) = 0 := by
    intro r hr
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hr] at hx
    simp [hk_zero x hx.1]
  have htail_xk_zero : ∀ r, 3 ≤ r →
      (∫ x in (3 : ℝ)..r, x * k x) = 0 := by
    intro r hr
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hr] at hx
    simp [hk_zero x hx.1]
  have hF_eq_one : ∀ r, 3 ≤ r → F r = 1 := by
    intro r hr
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hk_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 3)
      (hk_cont.intervalIntegrable (μ := MeasureTheory.volume) 3 r)
    rw [htail_k_zero r hr, hkmass] at hadd
    simpa [F] using hadd.symm
  have hG_eq_sqrt : ∀ r, 3 ≤ r → G r = Real.sqrt 2 := by
    intro r hr
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hxk_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 3)
      (hxk_cont.intervalIntegrable (μ := MeasureTheory.volume) 3 r)
    rw [htail_xk_zero r hr, hkmoment] at hadd
    simpa [G] using hadd.symm
  have hF_le_one : ∀ r, 0 ≤ r → F r ≤ 1 := by
    intro r hr
    by_cases hsmall : r ≤ 3
    · have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hk_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 r)
        (hk_cont.intervalIntegrable (μ := MeasureTheory.volume) r 3)
      have htail : 0 ≤ ∫ x in r..3, k x := by
        apply intervalIntegral.integral_nonneg hsmall
        intro x hx
        exact hk_nonneg x (hr.trans hx.1)
      rw [hkmass] at hadd
      have hFadd : F r + (∫ x in r..3, k x) = 1 := by
        simpa [F] using hadd
      linarith
    · exact (hF_eq_one r (le_of_not_ge hsmall)).le
  have hk_pos_near : ∀ {x : ℝ}, 0 < x → x < (1 / 32 : ℝ) → 0 < k x := by
    intro x hx hxs
    rw [hk_tip x hxs.le]
    have hs : 0 < Real.sin (x / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · nlinarith [Real.pi_gt_three]
    positivity
  have hF_pos : ∀ r, 0 < r → 0 < F r := by
    intro r hr
    apply intervalIntegral.integral_pos hr hk_cont.continuousOn
    · intro x hx
      exact hk_nonneg x (le_of_lt hx.1)
    · by_cases hsmall : r ≤ (1 / 32 : ℝ)
      · refine ⟨r / 2, ⟨by linarith, by linarith⟩, hk_pos_near (by linarith) (by linarith)⟩
      · refine ⟨1 / 64, ⟨by norm_num, by linarith⟩, hk_pos_near (by norm_num) (by norm_num)⟩
  have hG_nonneg : ∀ r, 0 ≤ r → 0 ≤ G r := by
    intro r hr
    dsimp [G]
    apply intervalIntegral.integral_nonneg hr
    intro x hx
    exact mul_nonneg hx.1 (hk_nonneg x hx.1)
  have hF_tip : ∀ r, |r| ≤ (1 / 32 : ℝ) → F r = 1 - Real.cos (r / 2) := by
    intro r hr
    have hEq : EqOn k (fun x : ℝ => Real.sin (x / 2) / 2) (uIcc 0 r) := by
      intro x hx
      apply hk_tip
      rcases (mem_uIcc.mp hx) with hx' | hx'
      · have hrr : r ≤ (1 / 32 : ℝ) := le_trans (le_abs_self r) hr
        linarith [hx'.2]
      · have hzero : (0 : ℝ) ≤ 1 / 32 := by norm_num
        linarith [hx'.2]
    have hder : ∀ x ∈ uIcc (0 : ℝ) r,
        HasDerivAt (fun y : ℝ => 1 - Real.cos (y / 2))
          (Real.sin (x / 2) / 2) x := by
      intro x hx
      have hc := (Real.hasDerivAt_cos (x / 2)).comp x
        ((hasDerivAt_id x).div_const (2 : ℝ))
      have hs := (hasDerivAt_const x (1 : ℝ)).sub hc
      have hs' : HasDerivAt (fun y : ℝ => 1 - Real.cos (y / 2))
          (0 - (-Real.sin (x / 2) * (1 / 2))) x :=
        hs.congr_of_eventuallyEq (by
        filter_upwards [] with y
        simp [Function.comp_def])
      simpa [div_eq_mul_inv] using hs'
    calc
      F r = ∫ x in (0 : ℝ)..r, Real.sin (x / 2) / 2 := by
        dsimp [F]
        exact intervalIntegral.integral_congr hEq
      _ = (1 - Real.cos (r / 2)) - (1 - Real.cos (0 / 2)) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hder
          ((Real.continuous_sin.comp (continuous_id.div_const (2 : ℝ))).div_const (2 : ℝ)
            |>.intervalIntegrable _ _)
      _ = 1 - Real.cos (r / 2) := by simp
  have hw_zero : w 0 = 0 := by
    simp [w, F, G]
  have hw_tip : ∀ r, |r| ≤ (1 / 32 : ℝ) → w r = 2 * Real.sin (r / 2) := by
    intro r hr
    have hrI : -(1 / 32 : ℝ) ≤ r ∧ r ≤ (1 / 32 : ℝ) := abs_le.mp hr
    have hderiv_sin : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => 2 * Real.sin (y / 2)) (Real.cos (x / 2)) x := by
      intro x
      have hs := (Real.hasDerivAt_sin (x / 2)).comp x
        ((hasDerivAt_id x).div_const (2 : ℝ))
      have hm := (hasDerivAt_const x (2 : ℝ)).mul hs
      have hm' : HasDerivAt (fun y : ℝ => 2 * Real.sin (y / 2))
          (0 * (Real.sin ∘ fun z : ℝ => id z / 2) x +
            2 * (Real.cos (x / 2) * (1 / 2))) x :=
        hm.congr_of_eventuallyEq (by
        filter_upwards [] with y
        simp [Function.comp_def])
      have hscalar : 0 * (Real.sin ∘ fun z : ℝ => id z / 2) x +
          2 * (Real.cos (x / 2) * (1 / 2 : ℝ)) = Real.cos (x / 2) := by
        ring
      exact hscalar ▸ hm'
    have hder : ∀ x ∈ uIcc (0 : ℝ) r,
        HasDerivAt (fun y : ℝ => w y - 2 * Real.sin (y / 2)) 0 x := by
      intro x hx
      have hxabs : |x| ≤ (1 / 32 : ℝ) := by
        rcases (mem_uIcc.mp hx) with hx' | hx'
        · apply (abs_le).2
          constructor
          · linarith
          · exact hx'.2.trans hrI.2
        · apply (abs_le).2
          constructor
          · exact hrI.1.trans hx'.1
          · linarith
      have hFx := hF_tip x hxabs
      have hs := (hw_has x).sub (hderiv_sin x)
      have hscalar : (1 - F x) - Real.cos (x / 2) = 0 := by
        rw [hFx]
        ring
      have hs' : HasDerivAt (w - (fun y : ℝ => 2 * Real.sin (y / 2))) 0 x :=
        hscalar ▸ hs
      exact hs'.congr_of_eventuallyEq (by
        filter_upwards [] with y
        rfl)
    have hz := intervalIntegral.integral_eq_sub_of_hasDerivAt hder intervalIntegrable_const
    simp [hw_zero] at hz
    linarith
  have hG_pos : ∀ r, (1 / 32 : ℝ) < r → 0 < G r := by
    intro r hr
    apply intervalIntegral.integral_pos (a := (0 : ℝ)) (b := r) (by linarith)
      hxk_cont.continuousOn
    · intro x hx
      exact mul_nonneg (le_of_lt hx.1) (hk_nonneg x (le_of_lt hx.1))
    · refine ⟨1 / 64, ⟨by norm_num, by linarith⟩, ?_⟩
      exact mul_pos (by norm_num) (hk_pos_near (by norm_num) (by norm_num))
  have hw_tail : ∀ r, (3 : ℝ) ≤ r → w r = Real.sqrt 2 := by
    intro r hr
    dsimp [w]
    rw [hF_eq_one r hr, hG_eq_sqrt r hr]
    ring
  have hw_pos : ∀ r, 0 < r → 0 < w r := by
    intro r hr
    by_cases hsmall : r ≤ (1 / 32 : ℝ)
    · rw [hw_tip r (by simpa [abs_of_pos hr] using hsmall)]
      have hs : 0 < Real.sin (r / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · positivity
        · nlinarith [Real.pi_gt_three]
      positivity
    · have hG := hG_pos r (lt_of_not_ge hsmall)
      have hfirst : 0 ≤ r * (1 - F r) := by
        apply mul_nonneg (le_of_lt hr)
        linarith [hF_le_one r (le_of_lt hr)]
      dsimp [w]
      linarith
  refine ⟨(1 / 32 : ℝ), 3, w, by norm_num, by norm_num, hw_smooth, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hw_tip
  · exact hw_tail
  · exact hw_pos
  · intro r hr
    rw [hw_deriv]
    constructor
    · linarith [hF_le_one r hr]
    · linarith [hF_nonneg r hr]
  · intro r hr
    rw [hw_deriv]
    linarith [hF_pos r hr]
  · intro r hr
    rw [hw_second]
    exact neg_nonpos.mpr (hk_nonneg r hr)
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
