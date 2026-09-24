import PoincareConjecture.ParallelImplementation.ParabolicSmallTimeConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.InverseMetricSmallTimeConstants
theorem exists_inverse_metric_small_time
    (alpha C R W : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hC : 0 ≤ C) (hR : 0 < R) (hW : 0 ≤ W) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ T : ℝ, 0 < T → T ≤ delta →
        3*(T+8*T^(1-alpha/2))*R ≤ 1/2 ∧
        2*C*(648*(T+8*T^(1-alpha/2)) +
          2*W*(3*Real.sqrt T+16*T^((1-alpha)/2))^2)*R ≤ 1/2 :=
/- SWARM_PROOF_BEGIN -/
by
  let A : ℝ := 3 * R + 1296 * C * R + 4 * C * W * R
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have heps : 0 < (1 / 4 : ℝ) := by norm_num
  obtain ⟨delta, hdelta, hdelta1, hproj⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicSmallTimeConstants.exists_small_time_projection_bounds
      alpha A (1 / 4 : ℝ) ha ha1 hA heps
  refine ⟨delta, hdelta, hdelta1, ?_⟩
  intro T hT hTdelta
  let u : ℝ := T + 8 * T ^ (1 - alpha / 2)
  let v : ℝ := (3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)) ^ 2
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hv : 0 ≤ v := by
    dsimp [v]
    positivity
  have hprojT := hproj T hT hTdelta
  have hAu : A * u ≤ 1 / 4 := by
    simpa [u] using hprojT.1
  have hAv : A * v ≤ 1 / 4 := by
    simpa [v] using hprojT.2
  have hfirst : 3 * R * u ≤ 1 / 4 := by
    calc
      3 * R * u ≤ A * u := by
        dsimp [A]
        have : 0 ≤ (1296 * C * R + 4 * C * W * R) * u :=
          mul_nonneg (by positivity) hu
        nlinarith
      _ ≤ 1 / 4 := hAu
  have hsecond₁ : 1296 * C * R * u ≤ 1 / 4 := by
    calc
      1296 * C * R * u ≤ A * u := by
        dsimp [A]
        have : 0 ≤ (3 * R + 4 * C * W * R) * u :=
          mul_nonneg (by positivity) hu
        nlinarith
      _ ≤ 1 / 4 := hAu
  have hsecond₂ : 4 * C * W * R * v ≤ 1 / 4 := by
    calc
      4 * C * W * R * v ≤ A * v := by
        dsimp [A]
        have : 0 ≤ (3 * R + 1296 * C * R) * v :=
          mul_nonneg (by positivity) hv
        nlinarith
      _ ≤ 1 / 4 := hAv
  constructor
  · calc
      3 * (T + 8 * T ^ (1 - alpha / 2)) * R = 3 * R * u := by
        dsimp [u]
        ring
      _ ≤ 1 / 2 := by linarith [hfirst]
  · calc
      2 * C * (648 * (T + 8 * T ^ (1 - alpha / 2)) +
          2 * W * (3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)) ^ 2) * R =
          1296 * C * R * u + 4 * C * W * R * v := by
        dsimp [u, v]
        ring
      _ ≤ 1 / 2 := by linarith [hsecond₁, hsecond₂]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.InverseMetricSmallTimeConstants
