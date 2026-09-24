import PoincareConjecture.ParallelImplementation.ParabolicSmallTimeConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.QuasilinearSmallTimeClosure
theorem exists_small_time_quasilinear_closure
    (alpha C F R Kv Kg : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hC : 0 ≤ C) (hF : 0 ≤ F) (hR : 0 < R)
    (hKv : 0 ≤ Kv) (hKg : 0 ≤ Kg) (hdata : 2*C*F ≤ R) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ T : ℝ, 0 < T → T ≤ delta →
      let K := Kv*(T+8*T^(1-alpha/2)) +
        Kg*(3*Real.sqrt T+16*T^((1-alpha)/2))^2
      0 ≤ K ∧ 2*C*K*R ≤ 1/2 ∧ C*(F+K*R^2) ≤ R :=
/- SWARM_PROOF_BEGIN -/
by
  let A : ℝ := Kv + Kg
  let eps : ℝ := 1 / (8 * (C + 1) * R)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨delta, hdelta, hdelta1, hproj⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicSmallTimeConstants.exists_small_time_projection_bounds
      alpha A eps ha ha1 hA heps
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
  have hAu : A * u ≤ eps := by simpa [A, u] using hprojT.1
  have hAv : A * v ≤ eps := by simpa [A, v] using hprojT.2
  have hKu : Kv * u ≤ eps := by
    calc
      Kv * u ≤ A * u := by
        dsimp [A]
        exact mul_le_mul_of_nonneg_right (by linarith [hKg]) hu
      _ ≤ eps := hAu
  have hK2 : Kg * v ≤ eps := by
    calc
      Kg * v ≤ A * v := by
        dsimp [A]
        exact mul_le_mul_of_nonneg_right (by linarith [hKv]) hv
      _ ≤ eps := hAv
  have hKnn : 0 ≤ Kv * u + Kg * v :=
    add_nonneg (mul_nonneg hKv hu) (mul_nonneg hKg hv)
  have hKle : Kv * u + Kg * v ≤ 2 * eps := by
    calc
      Kv * u + Kg * v ≤ eps + eps := add_le_add hKu hK2
      _ = 2 * eps := by ring
  have hbudget : (C * R) * (2 * eps) ≤ 1 / 4 := by
    dsimp [eps]
    have hden : 0 < 8 * (C + 1) * R := by positivity
    field_simp
    nlinarith [hC]
  have hprod : C * (Kv * u + Kg * v) * R ≤ 1 / 4 := by
    calc
      C * (Kv * u + Kg * v) * R = (C * R) * (Kv * u + Kg * v) := by ring
      _ ≤ (C * R) * (2 * eps) :=
        mul_le_mul_of_nonneg_left hKle (mul_nonneg hC (le_of_lt hR))
      _ ≤ 1 / 4 := hbudget
  have hcontract : 2 * C * (Kv * u + Kg * v) * R ≤ 1 / 2 := by
    nlinarith [hprod]
  have hball : C * (F + (Kv * u + Kg * v) * R ^ 2) ≤ R := by
    have hCF : C * F ≤ R / 2 := by nlinarith [hdata]
    have hquad : C * (Kv * u + Kg * v) * R ^ 2 ≤ R / 4 := by
      calc
        C * (Kv * u + Kg * v) * R ^ 2 =
            (C * (Kv * u + Kg * v) * R) * R := by ring
        _ ≤ (1 / 4) * R := mul_le_mul_of_nonneg_right hprod (le_of_lt hR)
        _ = R / 4 := by ring
    nlinarith [hCF, hquad]
  change 0 ≤ Kv * u + Kg * v ∧
    2 * C * (Kv * u + Kg * v) * R ≤ 1 / 2 ∧
    C * (F + (Kv * u + Kg * v) * R ^ 2) ≤ R
  exact ⟨hKnn, hcontract, hball⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.QuasilinearSmallTimeClosure
