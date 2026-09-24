import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OperatorHessianContraction
open scoped BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
theorem exists_operator_hessian_contraction
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ∃ B : (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3 →L[ℝ] V) →L[ℝ] V,
      ‖B‖ ≤ 9 ∧ ∀ A H,
        B A H = ∑ i : Fin 3, ∑ j : Fin 3,
          (A (EuclideanSpace.single j 1)) i •
            H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
/- SWARM_PROOF_BEGIN -/
by
  let e (k : Fin 3) : E3 := EuclideanSpace.single k 1
  let f : (E3 →L[ℝ] E3) →ₗ[ℝ]
      (E3 →L[ℝ] E3 →L[ℝ] V) →ₗ[ℝ] V :=
    LinearMap.mk₂ ℝ
      (fun A H => ∑ i : Fin 3, ∑ j : Fin 3,
        (A (e j)) i • H (e i) (e j))
      (by
        intro A₁ A₂ H
        simp [Finset.sum_add_distrib, add_smul])
      (by
        intro c A H
        simp [Finset.smul_sum, smul_smul])
      (by
        intro A H₁ H₂
        simp [Finset.sum_add_distrib, smul_add])
      (by
        intro c A H
        simp [Finset.smul_sum, smul_smul, mul_comm])
  have hterm (A : E3 →L[ℝ] E3) (H : E3 →L[ℝ] E3 →L[ℝ] V)
      (i j : Fin 3) :
      ‖(A (e j)) i • H (e i) (e j)‖ ≤ ‖A‖ * ‖H‖ := by
    have he (k : Fin 3) : ‖e k‖ = 1 := by simp [e]
    have hA : ‖(A (e j)) i‖ ≤ ‖A‖ := by
      calc
        ‖(A (e j)) i‖ ≤ ‖A (e j)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖A‖ * ‖e j‖ := A.le_opNorm _
        _ = ‖A‖ := by rw [he j, mul_one]
    have hH : ‖H (e i) (e j)‖ ≤ ‖H‖ := by
      calc
        ‖H (e i) (e j)‖ ≤ ‖H (e i)‖ * ‖e j‖ := (H (e i)).le_opNorm _
        _ ≤ (‖H‖ * ‖e i‖) * ‖e j‖ := by
          exact mul_le_mul_of_nonneg_right (H.le_opNorm (e i)) (norm_nonneg _)
        _ = ‖H‖ := by rw [he i, he j]; ring
    calc
      ‖(A (e j)) i • H (e i) (e j)‖ = ‖(A (e j)) i‖ * ‖H (e i) (e j)‖ := norm_smul _ _
      _ ≤ ‖A‖ * ‖H‖ := by gcongr
  have hbound (A : E3 →L[ℝ] E3) (H : E3 →L[ℝ] E3 →L[ℝ] V) :
      ‖f A H‖ ≤ 9 * ‖A‖ * ‖H‖ := by
    calc
      ‖f A H‖ = ‖∑ i : Fin 3, ∑ j : Fin 3,
          (A (e j)) i • H (e i) (e j)‖ := rfl
      _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
          (A (e j)) i • H (e i) (e j)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          ‖(A (e j)) i • H (e i) (e j)‖ := by
            apply Finset.sum_le_sum
            intro i hi
            exact norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖A‖ * ‖H‖ := by
          gcongr with i j
          exact hterm A H i j
      _ = 9 * ‖A‖ * ‖H‖ := by simp [mul_assoc]; ring
  refine ⟨f.mkContinuous₂ 9 hbound, ?_, ?_⟩
  · exact LinearMap.mkContinuous₂_norm_le _ (by norm_num) hbound
  · intro A H
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OperatorHessianContraction
