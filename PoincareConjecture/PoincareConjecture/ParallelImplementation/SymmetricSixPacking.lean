import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SymmetricSixPacking
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_symmetric_six_packing :

    ∃ P : Mat →L[ℝ] E6, ‖P‖ ≤ 3 ∧
      (∀ m : Mat, (P m) 0 = m 0 0 ∧ (P m) 1 = m 1 1 ∧ (P m) 2 = m 2 2 ∧
        (P m) 3 = m 0 1 ∧ (P m) 4 = m 0 2 ∧ (P m) 5 = m 1 2) ∧
      (∀ q : E6, P (MorganTianLib.MetricCoefficient.symmetricSixMatrix q) = q) ∧
      ∀ m : Mat, (∀ i j, m i j = m j i) →
        MorganTianLib.MetricCoefficient.symmetricSixMatrix (P m) = m :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let B : Mat →ₗ[ℝ] E6 :=
    { toFun := fun m => WithLp.toLp 2 ![m 0 0, m 1 1, m 2 2, m 0 1, m 0 2, m 1 2]
      map_add' := by
        intro m n
        ext k
        fin_cases k <;> simp
      map_smul' := by
        intro c m
        ext k
        fin_cases k <;> simp }
  let P : Mat →L[ℝ] E6 := LinearMap.toContinuousLinearMap B
  have h00 (m : Mat) : |m 0 0| ≤ ‖m‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_le_pi_norm (m 0) 0).trans (norm_le_pi_norm m 0)
  have h11 (m : Mat) : |m 1 1| ≤ ‖m‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_le_pi_norm (m 1) 1).trans (norm_le_pi_norm m 1)
  have h22 (m : Mat) : |m 2 2| ≤ ‖m‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_le_pi_norm (m 2) 2).trans (norm_le_pi_norm m 2)
  have h01 (m : Mat) : |m 0 1| ≤ ‖m‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_le_pi_norm (m 0) 1).trans (norm_le_pi_norm m 0)
  have h02 (m : Mat) : |m 0 2| ≤ ‖m‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_le_pi_norm (m 0) 2).trans (norm_le_pi_norm m 0)
  have h12 (m : Mat) : |m 1 2| ≤ ‖m‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_le_pi_norm (m 1) 2).trans (norm_le_pi_norm m 1)
  have hbound (m : Mat) : ‖P m‖ ≤ 3 * ‖m‖ := by
    have hcoords :
        (P m 0) ^ 2 + (P m 1) ^ 2 + (P m 2) ^ 2 +
          (P m 3) ^ 2 + (P m 4) ^ 2 + (P m 5) ^ 2 ≤ 6 * ‖m‖ ^ 2 := by
      have hc0 : (P m 0) ^ 2 ≤ ‖m‖ ^ 2 := by
        have h := h00 m
        have hsq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg m)).2 h
        simpa [P, B, abs_sq] using hsq
      have hc1 : (P m 1) ^ 2 ≤ ‖m‖ ^ 2 := by
        have h := h11 m
        have hsq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg m)).2 h
        simpa [P, B, abs_sq] using hsq
      have hc2 : (P m 2) ^ 2 ≤ ‖m‖ ^ 2 := by
        have h := h22 m
        have hsq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg m)).2 h
        simpa [P, B, abs_sq] using hsq
      have hc3 : (P m 3) ^ 2 ≤ ‖m‖ ^ 2 := by
        have h := h01 m
        have hsq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg m)).2 h
        simpa [P, B, abs_sq] using hsq
      have hc4 : (P m 4) ^ 2 ≤ ‖m‖ ^ 2 := by
        have h := h02 m
        have hsq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg m)).2 h
        simpa [P, B, abs_sq] using hsq
      have hc5 : (P m 5) ^ 2 ≤ ‖m‖ ^ 2 := by
        have h := h12 m
        have hsq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg m)).2 h
        simpa [P, B, abs_sq] using hsq
      nlinarith
    have hnorm : ‖P m‖ ^ 2 =
        (P m 0) ^ 2 + (P m 1) ^ 2 + (P m 2) ^ 2 +
          (P m 3) ^ 2 + (P m 4) ^ 2 + (P m 5) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ]
      ring
    apply (sq_le_sq₀ (norm_nonneg (P m)) (by positivity)).mp
    nlinarith [hnorm, hcoords]
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · exact ContinuousLinearMap.opNorm_le_bound P (by norm_num) hbound
  · intro m
    refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩⟩
    all_goals simp [P, B]
  · intro q
    ext k
    fin_cases k <;> simp [P, B, MorganTianLib.MetricCoefficient.symmetricSixMatrix]
  · intro m hsym
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, B, MorganTianLib.MetricCoefficient.symmetricSixMatrix] <;>
        first | rfl | exact hsym _ _
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SymmetricSixPacking
