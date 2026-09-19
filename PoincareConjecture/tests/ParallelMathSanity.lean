import PoincareConjecture.ParallelMath
set_option autoImplicit false
noncomputable section
open Set
open PoincareConjecture.ParallelMath
/-- A zero scalar coefficient recovers the actual linear comparison solution. -/
example (k a s t : ℝ) : comparisonSolution (fun _ => 0) k a s t = a-k*(t-s) := by
  simp [comparisonSolution, rateIntegral]
/-- An actual three-dimensional identity matrix satisfies the positive quadratic-form criterion. -/
example (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < quadraticForm (fun i j : Fin 3 => if i=j then 1 else 0) v := by
  apply positive_quadraticForm_of_small_frobenius_error
    (fun i j : Fin 3 => if i=j then 1 else 0) 0 (by norm_num) (by norm_num) ?_ v hv
  simp
/-- Zero-edge metric chains are included, rather than silently excluded. -/
example {X : Type*} [PseudoMetricSpace X] (x : X) : dist x x ≤ (0 : ℝ) := by
  exact finite_chain_dist_le 0 (fun _ => x)
