import PoincareConjecture.ParallelMath.Quantitative
set_option autoImplicit false
noncomputable section
open Set PoincareConjecture.ParallelMath.Quantitative
open scoped BigOperators
/-- **Math.** The contraction bound applies in actual dimension three. -/
example (A : Fin 3 → Fin 3 → ℝ) (v w : Fin 3 → ℝ) :
    (∑ i, ∑ j, A i j*v i*w j)^2 ≤
      (∑ i, ∑ j, (A i j)^2)*(∑ i, (v i)^2)*(∑ j, (w j)^2) :=
  bilinear_frobenius_sq_bound A v w
/-- **Math.** Zero-length partitions are included. -/
example (f : unitInterval → ℝ) (h : eVariationOn f univ ≠ ⊤)
    (t : Fin 1 → unitInterval) (ht : Monotone t) :
    (∑ i : Fin 0, dist (f (t i.castSucc)) (f (t i.succ))) ≤ (eVariationOn f univ).toReal :=
  dist_partition_sum_le_variation f h 0 t ht
