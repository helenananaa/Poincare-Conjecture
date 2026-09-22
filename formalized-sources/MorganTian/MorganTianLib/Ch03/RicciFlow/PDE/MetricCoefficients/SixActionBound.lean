import Mathlib
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Euclidean operator bound for the explicit symmetric six-coordinate action. -/
theorem six_action_bound (q : E6) (v : E3) :
    ‖(WithLp.toLp 2 (fun i : Fin 3 => ∑ j : Fin 3,
      (!![q 0, q 3, q 4; q 3, q 1, q 5; q 4, q 5, q 2] : Matrix (Fin 3) (Fin 3) ℝ) i j*v j) : E3)‖
      ≤ 3*‖q‖*‖v‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let r0 : E3 := WithLp.toLp 2 ![q 0, q 3, q 4]
  let r1 : E3 := WithLp.toLp 2 ![q 3, q 1, q 5]
  let r2 : E3 := WithLp.toLp 2 ![q 4, q 5, q 2]
  let w : E3 := WithLp.toLp 2 (fun i : Fin 3 => ∑ j : Fin 3,
    (!![q 0, q 3, q 4; q 3, q 1, q 5; q 4, q 5, q 2] : Matrix (Fin 3) (Fin 3) ℝ) i j * v j)
  change ‖w‖ ≤ 3 * ‖q‖ * ‖v‖
  have hw0 : w 0 = inner ℝ r0 v := by
    simp [w, r0, PiLp.inner_apply, Fin.sum_univ_succ] <;> ring
  have hw1 : w 1 = inner ℝ r1 v := by
    simp [w, r1, PiLp.inner_apply, Fin.sum_univ_succ] <;> ring
  have hw2 : w 2 = inner ℝ r2 v := by
    simp [w, r2, PiLp.inner_apply, Fin.sum_univ_succ] <;> ring
  have hr0 : ‖r0‖ ^ 2 = q 0 ^ 2 + q 3 ^ 2 + q 4 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [r0, Fin.sum_univ_succ] <;> ring
  have hr1 : ‖r1‖ ^ 2 = q 3 ^ 2 + q 1 ^ 2 + q 5 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [r1, Fin.sum_univ_succ] <;> ring
  have hr2 : ‖r2‖ ^ 2 = q 4 ^ 2 + q 5 ^ 2 + q 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [r2, Fin.sum_univ_succ] <;> ring
  have hq : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 + q 4 ^ 2 + q 5 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have hc0 : (w 0) ^ 2 ≤ ‖r0‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [hw0]
    simpa [pow_two, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le r0 v
  have hc1 : (w 1) ^ 2 ≤ ‖r1‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [hw1]
    simpa [pow_two, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le r1 v
  have hc2 : (w 2) ^ 2 ≤ ‖r2‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [hw2]
    simpa [pow_two, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le r2 v
  have hrows : ‖r0‖ ^ 2 + ‖r1‖ ^ 2 + ‖r2‖ ^ 2 ≤ 2 * ‖q‖ ^ 2 := by
    rw [hr0, hr1, hr2, hq]
    nlinarith [sq_nonneg (q 0), sq_nonneg (q 1), sq_nonneg (q 2)]
  have hmul :
      (‖r0‖ ^ 2 + ‖r1‖ ^ 2 + ‖r2‖ ^ 2) * ‖v‖ ^ 2 ≤
        (2 * ‖q‖ ^ 2) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hrows (sq_nonneg ‖v‖)
  have hout : ‖w‖ ^ 2 ≤ (2 * ‖q‖ ^ 2) * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    nlinarith [hc0, hc1, hc2, hmul]
  apply (sq_le_sq₀ (norm_nonneg w) (by positivity)).mp
  nlinarith [hout, sq_nonneg (‖q‖ * ‖v‖)]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
