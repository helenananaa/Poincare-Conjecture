import Mathlib
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.IndependentAlgebra
open scoped BigOperators RealInnerProductSpace
theorem inverse_apply_norm_le_of_coercive
    {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsUnit A)
    (lam : ℝ) (hlam : 0 < lam)
    (hlower : ∀ v : EuclideanSpace ℝ n,
      lam * ‖v‖^2 ≤ inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap v) v)
    (v : EuclideanSpace ℝ n) :
    ‖(Matrix.toEuclideanLin A⁻¹).toContinuousLinearMap v‖ ≤ lam⁻¹ * ‖v‖ :=
/- SWARM_PROOF_BEGIN -/
by
  let x := (Matrix.toEuclideanLin A⁻¹).toContinuousLinearMap v
  have hx : (Matrix.toEuclideanLin A).toContinuousLinearMap x = v := by
    simp [x, Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp hA)]
  have hcoercive := hlower x
  rw [hx] at hcoercive
  have hinner : inner ℝ v x ≤ ‖v‖ * ‖x‖ := real_inner_le_norm v x
  have hmul : lam * ‖x‖ ^ 2 ≤ ‖v‖ * ‖x‖ := hcoercive.trans hinner
  change ‖x‖ ≤ lam⁻¹ * ‖v‖
  by_cases hzero : ‖x‖ = 0
  · have hxzero : x = 0 := norm_eq_zero.mp hzero
    have hvzero : v = 0 := by rw [← hx]; simp [hxzero]
    simp [hzero, hvzero]
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hzero)
    have hmul' : (lam * ‖x‖) * ‖x‖ ≤ ‖v‖ * ‖x‖ := by
      simpa [pow_two, mul_assoc] using hmul
    have hdiv : lam * ‖x‖ ≤ ‖v‖ := le_of_mul_le_mul_right hmul' hxpos
    have hbound : ‖x‖ ≤ ‖v‖ / lam :=
      (le_div_iff₀ hlam).2 (by simpa [mul_comm] using hdiv)
    simpa [x, div_eq_mul_inv, mul_comm] using hbound
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.IndependentAlgebra
