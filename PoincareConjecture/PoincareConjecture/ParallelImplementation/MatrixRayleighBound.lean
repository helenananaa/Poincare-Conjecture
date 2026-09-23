import PoincareConjecture.ParallelImplementation.MatrixComponentBound
import Mathlib
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.IndependentAlgebra
open scoped BigOperators RealInnerProductSpace
theorem rayleigh_bound_of_entry_bound
    {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i j, |A i j| ≤ C) (x : EuclideanSpace ℝ n) :
    |inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap x) x| ≤
      (Fintype.card n : ℝ) * C * ‖x‖^2 :=
/- SWARM_PROOF_BEGIN -/
by
  have hinner :
      inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap x) x =
        ∑ i, ∑ j, x i * A i j * x j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have hcomp (i : n) :
        (((Matrix.toEuclideanLin A).toContinuousLinearMap x) i) =
          ∑ j, A i j * x j := by
      simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    simp only [dotProduct, star_trivial, hcomp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hnorm : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq x
  rw [hinner, hnorm]
  exact quadratic_bound_of_entry_bound A C hC hA (fun i => x i)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.IndependentAlgebra
