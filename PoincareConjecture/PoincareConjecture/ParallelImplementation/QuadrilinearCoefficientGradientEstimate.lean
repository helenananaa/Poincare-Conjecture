import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.QuadrilinearCoefficientGradientEstimate
theorem quadrilinear_coefficient_gradient_estimate
    {Y A V Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] Z)
    (I : Y → A) (P : Y →L[ℝ] V) (M K R : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 < R)
    (hI : ∀ z : Y, ‖z‖ ≤ R → ‖I z‖ ≤ M)
    (hIL : ∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R → ‖I z-I w‖ ≤ K*‖z-w‖)
    (z w : Y) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖B (I z) (I z) (P z) (P z)-B (I w) (I w) (P w) (P w)‖ ≤
      (‖B‖*(M^2+2*M*K*R)*‖P‖^2)*(‖z‖+‖w‖)*‖z-w‖ :=
/- SWARM_PROOF_BEGIN -/
by
  have hB (a b : A) (c d : V) :
      ‖B a b c d‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by
    calc
      ‖B a b c d‖ ≤ ‖B a b c‖ * ‖d‖ := (B a b c).le_opNorm d
      _ ≤ (‖B a b‖ * ‖c‖) * ‖d‖ := by
        gcongr
        exact (B a b).le_opNorm c
      _ ≤ ((‖B a‖ * ‖b‖) * ‖c‖) * ‖d‖ := by
        gcongr
        exact (B a).le_opNorm b
      _ ≤ (((‖B‖ * ‖a‖) * ‖b‖) * ‖c‖) * ‖d‖ := by
        gcongr
        exact B.le_opNorm a
  have hP (x : Y) : ‖P x‖ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
  have hPd : ‖P z - P w‖ ≤ ‖P‖ * ‖z - w‖ := by
    simpa only [map_sub] using P.le_opNorm (z - w)
  have hIzw : ‖I z - I w‖ ≤ K * ‖z - w‖ := hIL z w hz hw
  have hnormsq : ‖z‖ ^ 2 ≤ R * (‖z‖ + ‖w‖) := by
    rw [pow_two]
    calc
      ‖z‖ * ‖z‖ ≤ R * ‖z‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg z)
      _ ≤ R * (‖z‖ + ‖w‖) := by
        gcongr
        exact le_add_of_nonneg_right (norm_nonneg w)

  have he1 :
      B (I z) (I z) (P z) (P z) - B (I w) (I z) (P z) (P z) =
        B (I z - I w) (I z) (P z) (P z) := by
    rw [map_sub]
    rfl
  have he2 :
      B (I w) (I z) (P z) (P z) - B (I w) (I w) (P z) (P z) =
        B (I w) (I z - I w) (P z) (P z) := by
    rw [map_sub]
    rfl
  have he3 :
      B (I w) (I w) (P z) (P z) - B (I w) (I w) (P w) (P z) =
        B (I w) (I w) (P z - P w) (P z) := by
    rw [map_sub]
    rfl
  have he4 :
      B (I w) (I w) (P w) (P z) - B (I w) (I w) (P w) (P w) =
        B (I w) (I w) (P w) (P z - P w) := by
    rw [map_sub]

  let e1 := B (I z) (I z) (P z) (P z) - B (I w) (I z) (P z) (P z)
  let e2 := B (I w) (I z) (P z) (P z) - B (I w) (I w) (P z) (P z)
  let e3 := B (I w) (I w) (P z) (P z) - B (I w) (I w) (P w) (P z)
  let e4 := B (I w) (I w) (P w) (P z) - B (I w) (I w) (P w) (P w)
  let bnorm : ℝ := ‖B‖
  let pnorm : ℝ := ‖P‖
  let diffNorm : ℝ := ‖z - w‖
  let sumNorm : ℝ := ‖z‖ + ‖w‖

  have he1bound : ‖e1‖ ≤ bnorm * (M * K * R) * pnorm ^ 2 * sumNorm * diffNorm := by
    dsimp [e1, bnorm, pnorm, diffNorm, sumNorm]
    rw [he1]
    calc
      ‖B (I z - I w) (I z) (P z) (P z)‖ ≤
          ‖B‖ * ‖I z - I w‖ * ‖I z‖ * ‖P z‖ * ‖P z‖ := hB _ _ _ _
      _ ≤ ‖B‖ * (K * ‖z - w‖) * M * (‖P‖ * ‖z‖) * (‖P‖ * ‖z‖) := by
        gcongr
        · exact hI z hz
        · exact hP z
        · exact hP z
      _ = ‖B‖ * (M * K) * ‖P‖ ^ 2 * ‖z‖ ^ 2 * ‖z - w‖ := by ring
      _ ≤ ‖B‖ * (M * K) * ‖P‖ ^ 2 * (R * (‖z‖ + ‖w‖)) * ‖z - w‖ := by
        gcongr
      _ = ‖B‖ * (M * K * R) * ‖P‖ ^ 2 * (‖z‖ + ‖w‖) * ‖z - w‖ := by ring

  have he2bound : ‖e2‖ ≤ bnorm * (M * K * R) * pnorm ^ 2 * sumNorm * diffNorm := by
    dsimp [e2, bnorm, pnorm, diffNorm, sumNorm]
    rw [he2]
    calc
      ‖B (I w) (I z - I w) (P z) (P z)‖ ≤
          ‖B‖ * ‖I w‖ * ‖I z - I w‖ * ‖P z‖ * ‖P z‖ := hB _ _ _ _
      _ ≤ ‖B‖ * M * (K * ‖z - w‖) * (‖P‖ * ‖z‖) * (‖P‖ * ‖z‖) := by
        gcongr
        · exact hI w hw
        · exact hP z
        · exact hP z
      _ = ‖B‖ * (M * K) * ‖P‖ ^ 2 * ‖z‖ ^ 2 * ‖z - w‖ := by ring
      _ ≤ ‖B‖ * (M * K) * ‖P‖ ^ 2 * (R * (‖z‖ + ‖w‖)) * ‖z - w‖ := by
        gcongr
      _ = ‖B‖ * (M * K * R) * ‖P‖ ^ 2 * (‖z‖ + ‖w‖) * ‖z - w‖ := by ring

  have he3bound : ‖e3‖ ≤ bnorm * M ^ 2 * pnorm ^ 2 * ‖z‖ * diffNorm := by
    dsimp [e3, bnorm, pnorm, diffNorm]
    rw [he3]
    calc
      ‖B (I w) (I w) (P z - P w) (P z)‖ ≤
          ‖B‖ * ‖I w‖ * ‖I w‖ * ‖P z - P w‖ * ‖P z‖ := hB _ _ _ _
      _ ≤ ‖B‖ * M * M * (‖P‖ * ‖z - w‖) * (‖P‖ * ‖z‖) := by
        gcongr
        · exact hI w hw
        · exact hI w hw
        · exact hP z
      _ = ‖B‖ * M ^ 2 * ‖P‖ ^ 2 * ‖z‖ * ‖z - w‖ := by ring

  have he4bound : ‖e4‖ ≤ bnorm * M ^ 2 * pnorm ^ 2 * ‖w‖ * diffNorm := by
    dsimp [e4, bnorm, pnorm, diffNorm]
    rw [he4]
    calc
      ‖B (I w) (I w) (P w) (P z - P w)‖ ≤
          ‖B‖ * ‖I w‖ * ‖I w‖ * ‖P w‖ * ‖P z - P w‖ := hB _ _ _ _
      _ ≤ ‖B‖ * M * M * (‖P‖ * ‖w‖) * (‖P‖ * ‖z - w‖) := by
        gcongr
        · exact hI w hw
        · exact hI w hw
        · exact hP w
      _ = ‖B‖ * M ^ 2 * ‖P‖ ^ 2 * ‖w‖ * ‖z - w‖ := by ring

  let q0 := B (I z) (I z) (P z) (P z)
  let q1 := B (I w) (I z) (P z) (P z)
  let q2 := B (I w) (I w) (P z) (P z)
  let q3 := B (I w) (I w) (P w) (P z)
  let q4 := B (I w) (I w) (P w) (P w)
  have htri : ‖q0 - q4‖ ≤ ‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖ := by
    calc
      ‖q0 - q4‖ = dist q0 q4 := by simp only [dist_eq_norm]
      _ ≤ dist q0 q1 + dist q1 q4 := dist_triangle _ _ _
      _ ≤ dist q0 q1 + (dist q1 q2 + dist q2 q4) := by
        exact add_le_add_right (dist_triangle q1 q2 q4) (dist q0 q1)
      _ ≤ dist q0 q1 + (dist q1 q2 + (dist q2 q3 + dist q3 q4)) := by
        exact add_le_add_right
          (add_le_add_right (dist_triangle q2 q3 q4) (dist q1 q2)) (dist q0 q1)
      _ = ‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖ := by
        simp only [dist_eq_norm, q0, q1, q2, q3, q4, e1, e2, e3, e4]
        ring

  calc
    ‖B (I z) (I z) (P z) (P z) - B (I w) (I w) (P w) (P w)‖ ≤
        ‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖ := by
      simpa only [q0, q4] using htri
    _ ≤ bnorm * (M * K * R) * pnorm ^ 2 * sumNorm * diffNorm +
        bnorm * (M * K * R) * pnorm ^ 2 * sumNorm * diffNorm +
        bnorm * M ^ 2 * pnorm ^ 2 * ‖z‖ * diffNorm +
        bnorm * M ^ 2 * pnorm ^ 2 * ‖w‖ * diffNorm := by
      gcongr
    _ = (‖B‖ * (M ^ 2 + 2 * M * K * R) * ‖P‖ ^ 2) *
        (‖z‖ + ‖w‖) * ‖z - w‖ := by
      dsimp [bnorm, pnorm, diffNorm, sumNorm]
      ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.QuadrilinearCoefficientGradientEstimate
