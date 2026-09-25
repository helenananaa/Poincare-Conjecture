import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixHessianCoordinateEncoding
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open MorganTianLib.MetricCoefficient
theorem exists_hessian_entries :

    ∃ J : (E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] Second, ‖J‖ ≤ 1 ∧
      (∀ (H : E3 →L[ℝ] E3 →L[ℝ] E6) (a b i j : Idx),
        J H a b i j = symmetricSixMatrix (H (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j) ∧
      (∀ H a b i j, J H a b i j = J H a b j i) ∧
      ∀ H, (∀ v w : E3, H v w = H w v) → ∀ a b i j, J H a b i j = J H b a i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let Jlin : (E3 →L[ℝ] E3 →L[ℝ] E6) →ₗ[ℝ] Second :=
    { toFun := fun H a b i j =>
        symmetricSixMatrix (H (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j
      map_add' := by
        intro H K
        ext a b i j
        fin_cases i <;> fin_cases j <;> simp [symmetricSixMatrix]
      map_smul' := by
        intro c H
        ext a b i j
        fin_cases i <;> fin_cases j <;> simp [symmetricSixMatrix] }
  let J : (E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] Second :=
    Jlin.toContinuousLinearMap
  have hcoord (q : E6) (k : Fin 6) : ‖q k‖ ≤ ‖q‖ := by
    have hsq : (q k) ^ 2 ≤ ‖q‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (fun l hl => sq_nonneg (q l)) (Finset.mem_univ k)
    have habs : |q k| ≤ ‖q‖ :=
      (sq_le_sq₀ (abs_nonneg _) (norm_nonneg q)).1 (by simpa [sq_abs] using hsq)
    simpa [Real.norm_eq_abs] using habs
  have hsix (q : E6) (i j : Idx) :
      ‖symmetricSixMatrix q i j‖ ≤ ‖q‖ := by
    fin_cases i <;> fin_cases j <;>
      simp [symmetricSixMatrix] <;> exact hcoord q _
  have hentry (H : E3 →L[ℝ] E3 →L[ℝ] E6) (a b i j : Idx) :
      ‖symmetricSixMatrix
          (H (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j‖ ≤ ‖H‖ := by
    calc
      ‖symmetricSixMatrix
          (H (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j‖ ≤
          ‖H (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)‖ := hsix _ _ _
      _ ≤ ‖H‖ := by
        calc
          ‖H (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)‖ ≤
              ‖H (EuclideanSpace.single a 1)‖ *
                ‖EuclideanSpace.single b (1 : ℝ)‖ :=
            (H (EuclideanSpace.single a 1)).le_opNorm _
          _ ≤ (‖H‖ * ‖EuclideanSpace.single a (1 : ℝ)‖) *
                ‖EuclideanSpace.single b (1 : ℝ)‖ :=
            mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
          _ = ‖H‖ := by simp
  have pi_sup_bound {α β : Type} [Fintype α] [NormedAddCommGroup β]
      (f : α → β) (C : ℝ) (hC : 0 ≤ C)
      (hf : ∀ a, ‖f a‖ ≤ C) :
      (↑(Finset.univ.sup fun a => ‖f a‖₊) : ℝ) ≤ C := by
    rw [← Real.coe_toNNReal C hC]
    apply NNReal.coe_le_coe.mpr
    apply Finset.sup_le
    intro a ha
    apply NNReal.coe_le_coe.mp
    simpa only [coe_nnnorm, Real.coe_toNNReal C hC] using hf a
  have hbound (H : E3 →L[ℝ] E3 →L[ℝ] E6) : ‖Jlin H‖ ≤ ‖H‖ := by
    change (↑(Finset.univ.sup fun a : Idx => ‖Jlin H a‖₊) : ℝ) ≤ ‖H‖
    apply pi_sup_bound _ ‖H‖ (norm_nonneg H)
    intro a
    change (↑(Finset.univ.sup fun b : Idx => ‖fun i j => Jlin H a b i j‖₊) : ℝ) ≤ ‖H‖
    apply pi_sup_bound _ ‖H‖ (norm_nonneg H)
    intro b
    change (↑(Finset.univ.sup fun i : Idx => ‖fun j => Jlin H a b i j‖₊) : ℝ) ≤ ‖H‖
    apply pi_sup_bound _ ‖H‖ (norm_nonneg H)
    intro i
    change (↑(Finset.univ.sup fun j : Idx => ‖Jlin H a b i j‖₊) : ℝ) ≤ ‖H‖
    apply pi_sup_bound _ ‖H‖ (norm_nonneg H)
    intro j
    exact hentry H a b i j
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound J (by norm_num)
    intro H
    change ‖Jlin H‖ ≤ 1 * ‖H‖
    simpa using hbound H
  · intro H a b i j
    rfl
  · intro H a b i j
    change symmetricSixMatrix
        (H (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j =
      symmetricSixMatrix
        (H (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) j i
    fin_cases i <;> fin_cases j <;> simp [symmetricSixMatrix]
  · intro H hsym a b i j
    change symmetricSixMatrix
        (H (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j =
      symmetricSixMatrix
        (H (EuclideanSpace.single b 1) (EuclideanSpace.single a 1)) i j
    rw [hsym]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixHessianCoordinateEncoding
