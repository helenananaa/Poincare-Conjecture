import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ParabolicSmallTimeConstants
/-- Both genuine low-order projection bounds vanish as the slab length tends to zero. -/
theorem exists_small_time_projection_bounds
    (alpha A eps : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hA : 0 ≤ A) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∀ T : ℝ, 0 < T → T ≤ delta →
      A*(T+8*T^(1-alpha/2)) ≤ eps ∧
      A*(3*Real.sqrt T+16*T^((1-alpha)/2))^2 ≤ eps :=
/- SWARM_PROOF_BEGIN -/
by
  let p : ℝ := 1 - alpha / 2
  let q : ℝ := (1 - alpha) / 2
  let f : ℝ → ℝ := fun T => A * (T + 8 * T ^ p)
  let g : ℝ → ℝ := fun T => A * (3 * Real.sqrt T + 16 * T ^ q) ^ 2
  have hp : 0 < p := by dsimp [p]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hfcont : ContinuousAt f 0 := by
    dsimp [f]
    exact continuousAt_const.mul
      (continuousAt_id.add (continuousAt_const.mul
        ((Real.continuous_rpow_const hp.le).continuousAt)))
  have hgcont : ContinuousAt g 0 := by
    dsimp [g]
    have hsqrt : ContinuousAt Real.sqrt 0 := Real.continuous_sqrt.continuousAt
    have hpow : ContinuousAt (fun T : ℝ => T ^ q) 0 :=
      (Real.continuous_rpow_const hq.le).continuousAt
    have hbase : ContinuousAt (fun T : ℝ => 3 * Real.sqrt T + 16 * T ^ q) 0 := by
      exact (continuousAt_const.mul hsqrt).add (continuousAt_const.mul hpow)
    change ContinuousAt (fun T : ℝ => A * (3 * Real.sqrt T + 16 * T ^ q) ^ 2) 0
    exact continuousAt_const.mul (hbase.pow 2)
  have hf0 : f 0 = 0 := by
    simp [f, p, Real.zero_rpow (ne_of_gt hp)]
  have hg0 : g 0 = 0 := by
    simp [g, q, Real.zero_rpow (ne_of_gt hq)]
  obtain ⟨r₁, hr₁, hnear₁⟩ := Metric.continuousAt_iff.mp hfcont eps heps
  obtain ⟨r₂, hr₂, hnear₂⟩ := Metric.continuousAt_iff.mp hgcont eps heps
  let r : ℝ := min r₁ r₂
  let delta : ℝ := min 1 (r / 2)
  have hr : 0 < r := by dsimp [r]; exact lt_min hr₁ hr₂
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta_le : delta ≤ 1 := by dsimp [delta]; exact min_le_left _ _
  refine ⟨delta, hdelta, hdelta_le, ?_⟩
  intro T hT hTdelta
  have hTd : dist T (0 : ℝ) < r₁ := by
    dsimp [delta, r] at hTdelta
    have : T ≤ r / 2 := le_trans hTdelta (min_le_right _ _)
    dsimp [r] at this
    have hhalf : r / 2 ≤ r₁ / 2 := by
      exact div_le_div_of_nonneg_right (min_le_left r₁ r₂) (by norm_num)
    have : T < r₁ := by linarith
    simpa [Real.dist_eq, abs_of_pos hT] using this
  have hTd₂ : dist T (0 : ℝ) < r₂ := by
    dsimp [delta, r] at hTdelta
    have : T ≤ r / 2 := le_trans hTdelta (min_le_right _ _)
    dsimp [r] at this
    have hhalf : r / 2 ≤ r₂ / 2 := by
      exact div_le_div_of_nonneg_right (min_le_right r₁ r₂) (by norm_num)
    have : T < r₂ := by linarith
    simpa [Real.dist_eq, abs_of_pos hT] using this
  have hfv := hnear₁ hTd
  have hgv := hnear₂ hTd₂
  have hfnn : 0 ≤ f T := by
    dsimp [f]
    apply mul_nonneg hA
    apply add_nonneg (le_of_lt hT)
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hT) _)
  have hgnn : 0 ≤ g T := by
    dsimp [g]
    apply mul_nonneg hA
    exact sq_nonneg _
  constructor
  · have : dist (f T) 0 < eps := by simpa [hf0] using hfv
    have : f T < eps := by simpa [Real.dist_eq, abs_of_nonneg hfnn] using this
    change f T ≤ eps
    exact le_of_lt this
  · have : dist (g T) 0 < eps := by simpa [hg0] using hgv
    have : g T < eps := by simpa [Real.dist_eq, abs_of_nonneg hgnn] using this
    change g T ≤ eps
    exact le_of_lt this
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ParabolicSmallTimeConstants
