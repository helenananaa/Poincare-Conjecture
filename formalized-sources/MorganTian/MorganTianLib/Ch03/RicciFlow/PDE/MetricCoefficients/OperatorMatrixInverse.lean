import Mathlib
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- The canonical operator inverse agrees with the actual nonsingular inverse of its matrix. -/
theorem operator_matrix_inverse (A : E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) :
    (fun i j : Fin 3 => (A.inverse (EuclideanSpace.single j 1)) i) =
      (@Inv.inv (Matrix (Fin 3) (Fin 3) ℝ) Matrix.inv
        (fun i j : Fin 3 => (A (EuclideanSpace.single j 1)) i)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨e, he, he_inv⟩ := coercive_operator_inverse A c hc hA
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    LinearMap.toMatrix b b (A : E3 →ₗ[ℝ] E3)
  let N : Matrix (Fin 3) (Fin 3) ℝ :=
    LinearMap.toMatrix b b (e.symm.toLinearEquiv.toLinearMap)
  have hM : ∀ i j : Fin 3, M i j = (A (EuclideanSpace.single j 1)) i := by
    intro i j
    simp [M, b, LinearMap.toMatrix_apply]
  have hN : ∀ i j : Fin 3,
      N i j = (e.symm.toContinuousLinearMap (EuclideanSpace.single j 1)) i := by
    intro i j
    simp [N, b, LinearMap.toMatrix_apply]
  have he_lin : e.toLinearEquiv.toLinearMap = (A : E3 →ₗ[ℝ] E3) := by
    exact congrArg ContinuousLinearMap.toLinearMap he
  have hNM : N * M = 1 := by
    rw [← LinearMap.toMatrix_mul]
    rw [← he_lin]
    have hcomp :
        e.symm.toLinearEquiv.toLinearMap * e.toLinearEquiv.toLinearMap =
          LinearMap.id := by
      ext x
      simp
    rw [hcomp]
    simp
  have hinv : M⁻¹ = N := Matrix.inv_eq_left_inv hNM
  have hAi : A.inverse = e.symm.toContinuousLinearMap := by
    rw [← he]
    exact ContinuousLinearMap.inverse_equiv e
  have hMeq : M = (fun i j : Fin 3 => (A (EuclideanSpace.single j 1)) i) := by
    funext i j
    exact hM i j
  have hNeq : N = (fun i j : Fin 3 =>
      (e.symm.toContinuousLinearMap (EuclideanSpace.single j 1)) i) := by
    funext i j
    exact hN i j
  rw [hAi, ← hNeq]
  -- The corrected statement explicitly fixes the Matrix inverse instance.
  rw [← hMeq]
  exact hinv.symm
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
