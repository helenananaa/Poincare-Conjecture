import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SymmetricSixMatrixLinear
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_six_matrix_linear :

    ∃ L : E6 →L[ℝ] Mat, ‖L‖ ≤ 1 ∧ Function.Injective L ∧
      ∀ (q : E6) (i j : Idx), L q i j = symmetricSixMatrix q i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let Llin : E6 →ₗ[ℝ] Mat :=
    { toFun := fun q i j => symmetricSixMatrix q i j
      map_add' := by
        intro q r
        ext i j
        fin_cases i <;> fin_cases j <;> simp [symmetricSixMatrix]
      map_smul' := by
        intro c q
        ext i j
        fin_cases i <;> fin_cases j <;> simp [symmetricSixMatrix] }
  let L : E6 →L[ℝ] Mat := LinearMap.toContinuousLinearMap Llin
  have hcoord (q : E6) (k : Fin 6) : ‖q k‖ ≤ ‖q‖ := by
    have hsq : (q k) ^ 2 ≤ ‖q‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (fun l hl => sq_nonneg (q l)) (Finset.mem_univ k)
    have habs : |q k| ≤ ‖q‖ :=
      (sq_le_sq₀ (abs_nonneg _) (norm_nonneg q)).1 (by simpa [sq_abs] using hsq)
    simpa [Real.norm_eq_abs] using habs
  have hentry (q : E6) (i j : Idx) :
      ‖symmetricSixMatrix q i j‖ ≤ ‖q‖ := by
    fin_cases i <;> fin_cases j <;>
      simp [symmetricSixMatrix] <;> exact hcoord q _
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
  have hbound (q : E6) : ‖Llin q‖ ≤ ‖q‖ := by
    change (↑(Finset.univ.sup fun i : Idx => ‖Llin q i‖₊) : ℝ) ≤ ‖q‖
    apply pi_sup_bound _ ‖q‖ (norm_nonneg q)
    intro i
    change (↑(Finset.univ.sup fun j : Idx => ‖Llin q i j‖₊) : ℝ) ≤ ‖q‖
    apply pi_sup_bound _ ‖q‖ (norm_nonneg q)
    intro j
    exact hentry q i j
  refine ⟨L, ?_, ?_, ?_⟩
  · exact ContinuousLinearMap.opNorm_le_bound L (by norm_num) (by
      intro q
      change ‖Llin q‖ ≤ 1 * ‖q‖
      simpa using hbound q)
  · intro q r h
    ext k
    fin_cases k
    · have hk := congrFun (congrFun h 0) 0
      simpa [L, Llin, symmetricSixMatrix] using hk
    · have hk := congrFun (congrFun h 1) 1
      simpa [L, Llin, symmetricSixMatrix] using hk
    · have hk := congrFun (congrFun h 2) 2
      simpa [L, Llin, symmetricSixMatrix] using hk
    · have hk := congrFun (congrFun h 0) 1
      simpa [L, Llin, symmetricSixMatrix] using hk
    · have hk := congrFun (congrFun h 0) 2
      simpa [L, Llin, symmetricSixMatrix] using hk
    · have hk := congrFun (congrFun h 1) 2
      simpa [L, Llin, symmetricSixMatrix] using hk
  · intro q i j
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SymmetricSixMatrixLinear
