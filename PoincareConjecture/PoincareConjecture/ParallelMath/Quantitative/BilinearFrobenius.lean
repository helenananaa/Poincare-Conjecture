import Mathlib
import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff

/-- **Math.** Cauchy-Schwarz bounds the full mixed contraction, not just the diagonal quadratic form. -/
theorem bilinear_frobenius_sq_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (v : ι → ℝ) (w : κ → ℝ) :
    (∑ i, ∑ j, A i j * v i * w j)^2 ≤
      (∑ i, ∑ j, (A i j)^2) * (∑ i, (v i)^2) * (∑ j, (w j)^2) :=
/- SWARM_PROOF_BEGIN -/
by
  have hassoc :
      ∑ i, ∑ j, A i j * v i * w j = ∑ i, ∑ j, A i j * (v i * w j) := by
    simp_rw [mul_assoc]
  rw [hassoc]
  have hprod :
      ∑ i, ∑ j, A i j * (v i * w j)
        = ∑ p : ι × κ, A p.1 p.2 * (v p.1 * w p.2) :=
    (Fintype.sum_prod_type' fun i j => A i j * (v i * w j)).symm
  rw [hprod]
  refine (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × κ))
      (fun p => A p.1 p.2) (fun p => v p.1 * w p.2)).trans ?_
  refine le_of_eq ?_
  rw [mul_assoc]
  congr 1
  · exact Fintype.sum_prod_type' fun i j => (A i j)^2
  · calc
      ∑ p : ι × κ, (v p.1 * w p.2)^2
          = ∑ p : ι × κ, (v p.1)^2 * (w p.2)^2 := by
            simp_rw [mul_pow]
      _ = ∑ i, ∑ j, (v i)^2 * (w j)^2 :=
            Fintype.sum_prod_type' fun i j => (v i)^2 * (w j)^2
      _ = (∑ i, (v i)^2) * ∑ j, (w j)^2 :=
            (Fintype.sum_mul_sum (fun i => (v i)^2) (fun j => (w j)^2)).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative
