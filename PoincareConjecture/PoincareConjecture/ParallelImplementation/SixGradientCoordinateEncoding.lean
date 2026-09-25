import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixGradientCoordinateEncoding
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open MorganTianLib.MetricCoefficient
theorem exists_gradient_entries :

    ∃ D : (E3 →L[ℝ] E6) →L[ℝ] First, ‖D‖ ≤ 1 ∧
      (∀ (A : E3 →L[ℝ] E6) (a i j : Idx),
        D A a i j = symmetricSixMatrix (A (EuclideanSpace.single a 1)) i j) ∧
      ∀ (A : E3 →L[ℝ] E6) (a i j : Idx), D A a i j = D A a j i :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let L : (E3 →L[ℝ] E6) →ₗ[ℝ] First :=
    { toFun := fun A a i j =>
        symmetricSixMatrix (A (EuclideanSpace.single a 1)) i j
      map_add' := by
        intro A B
        funext a i j
        fin_cases i <;> fin_cases j <;> simp [symmetricSixMatrix]
      map_smul' := by
        intro c A
        funext a i j
        fin_cases i <;> fin_cases j <;> simp [symmetricSixMatrix] }
  have hqbound (q : E6) (k : Fin 6) : |q k| ≤ ‖q‖ := by
    simpa using
      (PiLp.norm_apply_le (p := 2) (x := q) k)
  have hsixbound (q : E6) (i j : Idx) :
      |symmetricSixMatrix q i j| ≤ ‖q‖ := by
    fin_cases i <;> fin_cases j <;>
      first
      | simpa [symmetricSixMatrix] using hqbound q 0
      | simpa [symmetricSixMatrix] using hqbound q 1
      | simpa [symmetricSixMatrix] using hqbound q 2
      | simpa [symmetricSixMatrix] using hqbound q 3
      | simpa [symmetricSixMatrix] using hqbound q 4
      | simpa [symmetricSixMatrix] using hqbound q 5
  have hbound (A : E3 →L[ℝ] E6) : ‖L A‖ ≤ ‖A‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro a
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro j
    calc
      ‖symmetricSixMatrix (A (EuclideanSpace.single a 1)) i j‖ ≤
          ‖A (EuclideanSpace.single a 1)‖ := by
            simpa [Real.norm_eq_abs] using hsixbound
              (A (EuclideanSpace.single a 1)) i j
      _ ≤ ‖A‖ * ‖EuclideanSpace.single a 1‖ := A.le_opNorm _
      _ = ‖A‖ := by simp
  let D : (E3 →L[ℝ] E6) →L[ℝ] First :=
    L.mkContinuous 1 (fun A => by simpa using hbound A)
  refine ⟨D, ?_, ?_, ?_⟩
  · exact LinearMap.mkContinuous_norm_le L zero_le_one
      (fun A => by simpa using hbound A)
  · intro A a i j
    simp [D, L]
  · intro A a i j
    fin_cases i <;> fin_cases j <;> simp [D, L, symmetricSixMatrix]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixGradientCoordinateEncoding
