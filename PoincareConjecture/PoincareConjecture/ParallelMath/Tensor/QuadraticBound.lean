import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- Frobenius norm controls quadratic evaluation in a finite orthonormal frame. -/
theorem quadraticForm_sq_le {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (v : ι → ℝ) :
    (quadraticForm A v)^2 ≤ (∑ i, ∑ j, (A i j)^2) * (∑ i, (v i)^2)^2 :=
/- SWARM_PROOF_BEGIN -/
by
  unfold quadraticForm
  have hassoc :
      ∑ i, ∑ j, A i j * v i * v j = ∑ i, ∑ j, A i j * (v i * v j) := by
    simp_rw [mul_assoc]
  rw [hassoc]
  have hprod :
      ∑ i, ∑ j, A i j * (v i * v j)
        = ∑ p : ι × ι, A p.1 p.2 * (v p.1 * v p.2) :=
    (Fintype.sum_prod_type' fun i j => A i j * (v i * v j)).symm
  rw [hprod]
  refine (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
      (fun p => A p.1 p.2) (fun p => v p.1 * v p.2)).trans ?_
  refine le_of_eq ?_
  congr 1
  · exact Fintype.sum_prod_type' fun i j => (A i j)^2
  · calc
      ∑ p : ι × ι, (v p.1 * v p.2)^2
          = ∑ p : ι × ι, (v p.1)^2 * (v p.2)^2 := by
            simp_rw [mul_pow]
      _ = ∑ i, ∑ j, (v i)^2 * (v j)^2 :=
            Fintype.sum_prod_type' fun i j => (v i)^2 * (v j)^2
      _ = (∑ i, (v i)^2) * ∑ j, (v j)^2 :=
            (Fintype.sum_mul_sum (fun i => (v i)^2) (fun j => (v j)^2)).symm
      _ = (∑ i, (v i)^2)^2 :=
            (pow_two _).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
