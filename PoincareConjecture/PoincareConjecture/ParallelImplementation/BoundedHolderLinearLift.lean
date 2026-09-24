import PoincareConjecture.ParallelImplementation.ParabolicIncrementBCF
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BoundedHolderLinearLift
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BoundedContinuousFunction
/-- Lift a linear bounded field with controlled actual increments into the full Holder graph. -/
theorem exists_bounded_holder_linear_lift
    {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T alpha M H : ℝ) (ha : 0 < alpha) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (P : X →ₗ[ℝ] (Slab T →ᵇ V))
    (hbound : ∀ z : X, ‖P z‖ ≤ M*‖z‖)
    (hholder : ∀ z : X, ∀ p q : Slab T,
      ‖P z p-P z q‖ ≤ (H*‖z‖)*parabolicRho p q ^ alpha) :
    ∃ Q : X →L[ℝ] ForcingJet V T, ‖Q‖ ≤ M+H ∧
      (∀ z : X, (Q z).1 = P z) ∧ ∀ z : X, Q z ∈ forcingGraph V T alpha := by
  classical
  have hex (z : X) :=
    PoincareConjecture.ParallelImplementation.ParabolicIncrementBCF.exists_bounded_parabolic_increment
      T alpha (H*‖z‖) ha (mul_nonneg hH (norm_nonneg _)) (P z) (P z).continuous (hholder z)
  choose inc hincnorm hinc using hex
  let Q0 : X →ₗ[ℝ] ForcingJet V T := {
    toFun := fun z => (P z, inc z)
    map_add' := by
      intro z w
      apply Prod.ext
      · exact P.map_add z w
      · apply BoundedContinuousFunction.ext
        intro p
        change inc (z+w) p = inc z p + inc w p
        rw [hinc, hinc, hinc, P.map_add]
        simp only [BoundedContinuousFunction.add_apply, smul_add, smul_sub]
        abel
    map_smul' := by
      intro c z
      apply Prod.ext
      · exact P.map_smul c z
      · apply BoundedContinuousFunction.ext
        intro p
        change inc (c • z) p = c • inc z p
        rw [hinc, hinc, P.map_smul]
        simp only [BoundedContinuousFunction.smul_apply, smul_sub, smul_smul]
        rw [mul_comm]
  }
  have hQ (z : X) : ‖Q0 z‖ ≤ (M+H)*‖z‖ := by
    change max ‖P z‖ ‖inc z‖ ≤ _
    apply max_le
    · exact (hbound z).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hH) (norm_nonneg _))
    · exact (hincnorm z).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) (norm_nonneg _))
  refine ⟨Q0.mkContinuous (M+H) hQ, LinearMap.mkContinuous_norm_le Q0 (add_nonneg hM hH) hQ, fun _ => rfl, ?_⟩
  intro z p
  exact hinc z p
end PoincareConjecture.ParallelImplementation.BoundedHolderLinearLift
