import PoincareConjecture.ParallelImplementation.CoerciveInverseBound
import Mathlib
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.IndependentAlgebra
open scoped BigOperators RealInnerProductSpace
theorem inverse_entry_abs_le_of_coercive
    {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsUnit A)
    (lam : ℝ) (hlam : 0 < lam)
    (hlower : ∀ v : EuclideanSpace ℝ n,
      lam * ‖v‖^2 ≤ inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap v) v)
    :
    ∀ i j, |A⁻¹ i j| ≤ lam⁻¹ :=
/- SWARM_PROOF_BEGIN -/
by
  intro i j
  let e : EuclideanSpace ℝ n := EuclideanSpace.single j 1
  let y : EuclideanSpace ℝ n :=
    (Matrix.toEuclideanLin A⁻¹).toContinuousLinearMap e
  have hbound := inverse_apply_norm_le_of_coercive A hA lam hlam hlower e
  have hcoord : |y i| ≤ ‖y‖ := by
    have h := abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ)) y
    simpa [EuclideanSpace.inner_single_left] using h
  have hentry : y i = A⁻¹ i j := by
    simp [y, e, Matrix.toLpLin_apply]
  calc
    |A⁻¹ i j| = |y i| := by rw [hentry]
    _ ≤ ‖y‖ := hcoord
    _ ≤ lam⁻¹ * ‖e‖ := hbound
    _ = lam⁻¹ := by simp [e]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.IndependentAlgebra
