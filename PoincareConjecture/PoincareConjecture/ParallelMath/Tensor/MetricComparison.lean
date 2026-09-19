import PoincareConjecture.ParallelMath.Tensor.QuadraticBound
import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- A small coefficient error from the identity gives two-sided quadratic-form bounds. -/
theorem metric_comparison_of_frobenius_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℝ) (epsilon : ℝ) (heps : 0 ≤ epsilon)
    (herror : (∑ i, ∑ j, (A i j - if i=j then 1 else 0)^2) ≤ epsilon^2) :
    ∀ v : ι → ℝ,
      (1-epsilon)*(∑ i, (v i)^2) ≤ quadraticForm A v ∧
      quadraticForm A v ≤ (1+epsilon)*(∑ i, (v i)^2) :=
/- SWARM_PROOF_BEGIN -/
by
  intro v
  set B : ι → ι → ℝ := fun i j => A i j - if i = j then 1 else 0
  set s : ℝ := ∑ i, (v i) ^ 2
  have hs : 0 ≤ s := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : quadraticForm B v = quadraticForm A v - s := by
    unfold quadraticForm B s
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, pow_two]
  have herr : (∑ i, ∑ j, (B i j) ^ 2) ≤ epsilon ^ 2 := by
    simpa [B] using herror
  have hsq : (quadraticForm B v) ^ 2 ≤ epsilon ^ 2 * s ^ 2 :=
    (quadraticForm_sq_le B v).trans (mul_le_mul_of_nonneg_right herr (sq_nonneg s))
  have hchain : (quadraticForm A v - s) ^ 2 ≤ (epsilon * s) ^ 2 := by
    rw [mul_pow, ← hB]
    exact hsq
  have htwo := abs_le_of_sq_le_sq' hchain (mul_nonneg heps hs)
  exact ⟨by linarith [htwo.1], by linarith [htwo.2]⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
