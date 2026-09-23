import PoincareConjecture.ParallelImplementation.MatrixRayleighBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OrthonormalRayleighBound
open scoped BigOperators RealInnerProductSpace
theorem rayleigh_bound_of_orthonormal_components
    {n V : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : OrthonormalBasis n ℝ V) (T : V →L[ℝ] V)
    (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i j, |inner ℝ (T (b i)) (b j)| ≤ C) (x : V) :
    |inner ℝ (T x) x| ≤ (Fintype.card n : ℝ) * C * ‖x‖^2 :=
/- SWARM_PROOF_BEGIN -/
by
  let A : Matrix n n ℝ := fun i j => inner ℝ (T (b j)) (b i)
  let y : EuclideanSpace ℝ n := b.repr x
  have hA : ∀ i j, |A i j| ≤ C := by
    intro i j
    simpa [A] using hT j i
  have hmatrix (i : n) :
      ((Matrix.toEuclideanLin A).toContinuousLinearMap y) i =
        ∑ j, A i j * y j := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  have hcoord : b.repr (T x) = (Matrix.toEuclideanLin A).toContinuousLinearMap y := by
    ext i
    rw [hmatrix]
    rw [OrthonormalBasis.repr_apply_apply]
    rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
    rw [inner_sum]
    simp [A, y, inner_smul_right, real_inner_comm, mul_comm]
  have hinner :
      inner ℝ (T x) x =
        inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap y) y := by
    rw [← b.repr.inner_map_map (T x) x, hcoord]
  have hnorm : ‖y‖ = ‖x‖ := by
    simp [y]
  rw [hinner]
  simpa [y, hnorm] using
    PoincareConjecture.ParallelImplementation.IndependentAlgebra.rayleigh_bound_of_entry_bound
      A C hC hA y
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OrthonormalRayleighBound
