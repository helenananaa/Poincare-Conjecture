import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.QuadraticFixedPointDataStability
theorem fixed_point_data_stability
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (D : X →L[ℝ] Y) (N : Y → X) (K R : ℝ)
    (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hLip : ∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖N z-N w‖ ≤ K*(‖z‖+‖w‖)*‖z-w‖)
    (hcontract : 2*‖D‖*K*R < 1)
    (f g : X) (z w : Y) (hzR : ‖z‖ ≤ R) (hwR : ‖w‖ ≤ R)
    (hz : z = D (f+N z)) (hw : w = D (g+N w)) :
    ‖z-w‖ ≤ (‖D‖/(1-2*‖D‖*K*R))*‖f-g‖ :=
/- SWARM_PROOF_BEGIN -/
by
  have hN : ‖N z - N w‖ ≤ (2 * K * R) * ‖z - w‖ := by
    calc
      ‖N z - N w‖ ≤ K * (‖z‖ + ‖w‖) * ‖z - w‖ := hLip z w hzR hwR
      _ ≤ K * (2 * R) * ‖z - w‖ := by
        gcongr
        linarith
      _ = (2 * K * R) * ‖z - w‖ := by ring
  have hbase : ‖z - w‖ ≤ ‖D‖ * (‖f - g‖ + ‖N z - N w‖) := by
    calc
      ‖z - w‖ = ‖D ((f - g) + (N z - N w))‖ := by
        conv_lhs => rw [hz, hw]
        congr 1
        rw [← map_sub]
        congr 1
        abel
      _ ≤ ‖D‖ * ‖(f - g) + (N z - N w)‖ := D.le_opNorm _
      _ ≤ ‖D‖ * (‖f - g‖ + ‖N z - N w‖) := by
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
  have hmain : ‖z - w‖ ≤ ‖D‖ * ‖f - g‖ + (2 * ‖D‖ * K * R) * ‖z - w‖ := by
    calc
      ‖z - w‖ ≤ ‖D‖ * (‖f - g‖ + ‖N z - N w‖) := hbase
      _ ≤ ‖D‖ * (‖f - g‖ + (2 * K * R) * ‖z - w‖) := by
        gcongr
      _ = ‖D‖ * ‖f - g‖ + (2 * ‖D‖ * K * R) * ‖z - w‖ := by ring
  have hden : 0 < 1 - 2 * ‖D‖ * K * R := by linarith [hcontract]
  have hmul : ‖z - w‖ * (1 - 2 * ‖D‖ * K * R) ≤ ‖D‖ * ‖f - g‖ := by
    nlinarith [hmain]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hden).2 hmul
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.QuadraticFixedPointDataStability
