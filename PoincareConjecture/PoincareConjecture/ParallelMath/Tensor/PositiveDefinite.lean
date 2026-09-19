import PoincareConjecture.ParallelMath.Tensor.MetricComparison
import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- The small-error quantitative metric comparison supplies strict positivity. -/
theorem positive_quadraticForm_of_small_frobenius_error
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℝ) (epsilon : ℝ) (heps0 : 0 ≤ epsilon) (heps1 : epsilon < 1)
    (herror : (∑ i, ∑ j, (A i j - if i=j then 1 else 0)^2) ≤ epsilon^2) :
    ∀ v : ι → ℝ, v ≠ 0 → 0 < quadraticForm A v :=
/- SWARM_PROOF_BEGIN -/
by
  intro v hv
  have hlo := (metric_comparison_of_frobenius_error A epsilon heps0 herror v).1
  rw [ne_eq, funext_iff, not_forall] at hv
  obtain ⟨i, hi⟩ := hv
  have hs : 0 < ∑ j, (v j) ^ 2 :=
    Finset.sum_pos' (fun _ _ => sq_nonneg _)
      ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have hcoef : 0 < 1 - epsilon := sub_pos.mpr heps1
  exact lt_of_lt_of_le (mul_pos hcoef hs) hlo
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
