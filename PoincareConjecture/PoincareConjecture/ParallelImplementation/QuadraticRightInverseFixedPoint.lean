import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint
/-- A genuine right inverse and quadratic Lipschitz estimate yield a closed-ball fixed point. -/
theorem quadratic_right_inverse_fixed_point
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (L : Y →L[ℝ] X) (D : X →L[ℝ] Y)
    (hLD : L.comp D = ContinuousLinearMap.id ℝ X)
    (N : Y → X) (hN0 : N 0 = 0) (f : X)
    (K R : ℝ) (hK : 0 ≤ K) (hR : 0 < R)
    (hLip : ∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖N z-N w‖ ≤ K*(‖z‖+‖w‖)*‖z-w‖)
    (hself : ‖D‖ * (‖f‖+K*R^2) ≤ R)
    (hcontract : 2*‖D‖*K*R < 1) :
    ∃ z : Y, ‖z‖ ≤ R ∧ z = D (f+N z) ∧ L z = f+N z ∧
      ∀ w : Y, ‖w‖ ≤ R → w = D (f+N w) → w = z :=
/- SWARM_PROOF_BEGIN -/
by
  let Φ : Y → Y := fun z => D (f + N z)
  let q : ℝ := 2 * ‖D‖ * K * R
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_lt : q < 1 := by
    simpa [q] using hcontract
  have hNquad (z : Y) (hz : ‖z‖ ≤ R) : ‖N z‖ ≤ K * ‖z‖ ^ 2 := by
    have hz0 : ‖(0 : Y)‖ ≤ R := by simpa using hR.le
    have hh := hLip z 0 hz hz0
    simpa [hN0, pow_two, mul_assoc] using hh
  have hPhi_ball (z : Y) (hz : ‖z‖ ≤ R) : ‖Φ z‖ ≤ R := by
    calc
      ‖Φ z‖ = ‖D (f + N z)‖ := rfl
      _ ≤ ‖D‖ * ‖f + N z‖ := D.le_opNorm _
      _ ≤ ‖D‖ * (‖f‖ + ‖N z‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ ≤ ‖D‖ * (‖f‖ + K * R ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact add_le_add_right (calc
          ‖N z‖ ≤ K * ‖z‖ ^ 2 := hNquad z hz
          _ ≤ K * R ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hK
            calc
              ‖z‖ ^ 2 = ‖z‖ * ‖z‖ := by rw [pow_two]
              _ ≤ R * R := mul_le_mul hz hz (norm_nonneg z) hR.le
              _ = R ^ 2 := (pow_two R).symm) _
      _ ≤ R := hself
  have hPhi_lip (z w : Y) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
      ‖Φ z - Φ w‖ ≤ q * ‖z - w‖ := by
    have hsum : ‖z‖ + ‖w‖ ≤ 2 * R := by nlinarith
    calc
      ‖Φ z - Φ w‖ = ‖D (N z - N w)‖ := by
        simp [Φ, map_sub, add_sub_add_left_eq_sub]
      _ ≤ ‖D‖ * ‖N z - N w‖ := D.le_opNorm _
      _ ≤ ‖D‖ * (K * (‖z‖ + ‖w‖) * ‖z - w‖) :=
        mul_le_mul_of_nonneg_left (hLip z w hz hw) (norm_nonneg _)
      _ ≤ q * ‖z - w‖ := by
        dsimp [q]
        calc
          ‖D‖ * (K * (‖z‖ + ‖w‖) * ‖z - w‖) ≤
              ‖D‖ * (K * (2 * R) * ‖z - w‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hsum hK
          _ = (2 * ‖D‖ * K * R) * ‖z - w‖ := by ring
  let s : Set Y := Metric.closedBall (0 : Y) R
  have hmem_norm {z : Y} (hz : z ∈ s) : ‖z‖ ≤ R := by
    simpa [s, Metric.mem_closedBall, dist_eq_norm] using hz
  have hsc : IsComplete s := by
    simpa [s] using
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : Y) R)).isComplete
  have hzero : (0 : Y) ∈ s := by
    simp [s, Metric.mem_closedBall, hR.le]
  let B := {z : Y // z ∈ s}
  let c : NNReal := ⟨q, hq_nonneg⟩
  have hc_val : (c : ℝ) = q := rfl
  let F : B → B := fun z => ⟨Φ z.1, by
    simpa [s, Metric.mem_closedBall, dist_eq_norm] using
      hPhi_ball z.1 (hmem_norm z.2)⟩
  letI : CompleteSpace B := hsc.completeSpace_coe
  have hF_lip : LipschitzWith c F := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (Φ z.1) (Φ w.1) ≤ (c : ℝ) * dist z.1 w.1
    have hh := hPhi_lip z.1 w.1 (hmem_norm z.2) (hmem_norm w.2)
    simpa [dist_eq_norm, hc_val] using hh
  have hc_lt : c < 1 := by
    apply NNReal.coe_lt_coe.mp
    simpa [hc_val] using hcontract
  have hF_contract : ContractingWith c F := ⟨hc_lt, hF_lip⟩
  obtain ⟨u, hu_fixed, _, _⟩ :=
    hF_contract.exists_fixedPoint ⟨0, hzero⟩ (edist_ne_top _ _)
  have hPhi_fixed : Φ u.1 = u.1 := by
    have hh := congrArg (fun x : B => x.1) hu_fixed
    simpa [F] using hh
  have hu_bound : ‖u.1‖ ≤ R := hmem_norm u.2
  have hLD_point : L (D (f + N u.1)) = f + N u.1 := by
    simpa using congrArg (fun T : X →L[ℝ] X => T (f + N u.1)) hLD
  have hL_u : L u.1 = f + N u.1 := by
    calc
      L u.1 = L (Φ u.1) := (congrArg L hPhi_fixed).symm
      _ = L (D (f + N u.1)) := rfl
      _ = f + N u.1 := hLD_point
  refine ⟨u.1, hu_bound, ?_, hL_u, ?_⟩
  · simpa [Φ] using hPhi_fixed.symm
  · intro w hw hfixed
    have hPhi_fixed_w : Φ w = w := by simpa [Φ] using hfixed.symm
    have hdiff : Φ w - Φ u.1 = w - u.1 := by rw [hPhi_fixed_w, hPhi_fixed]
    have hineq := hPhi_lip w u.1 hw hu_bound
    rw [hdiff] at hineq
    have hnorm : ‖w - u.1‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖w - u.1‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have hh := mul_lt_mul_of_pos_right hq_lt hpos
      have hh' : q * ‖w - u.1‖ < ‖w - u.1‖ := by simpa using hh
      exact (not_lt_of_ge hineq) hh'
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint
