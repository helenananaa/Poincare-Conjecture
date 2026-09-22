import Mathlib
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Actual faithful linear action of the six independent symmetric matrix entries. -/
theorem six_linear_action :
    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧
      ∀ (q : E6) (v : E3) (i : Fin 3), (E q v) i =
        ∑ j : Fin 3, (!![q 0, q 3, q 4; q 3, q 1, q 5; q 4, q 5, q 2] : Matrix (Fin 3) (Fin 3) ℝ) i j * v j :=
/- SWARM_PROOF_BEGIN -/
by
  let A : E6 →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    { toFun := fun q => !![q 0, q 3, q 4; q 3, q 1, q 5; q 4, q 5, q 2]
      map_add' := by
        intro q r
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_smul' := by
        intro c q
        ext i j
        fin_cases i <;> fin_cases j <;> simp }
  let B : E6 →ₗ[ℝ] (E3 →L[ℝ] E3) :=
    ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv :
      Matrix (Fin 3) (Fin 3) ℝ ≃ₗ[ℝ] (E3 →L[ℝ] E3)).toLinearMap.comp A
  let E : E6 →L[ℝ] (E3 →L[ℝ] E3) :=
    LinearMap.toContinuousLinearMap B
  have hE (q : E6) (v : E3) (i : Fin 3) :
      (E q v) i = ∑ j : Fin 3, (A q) i j * v j := by
    have h := congrFun (Matrix.ofLp_toEuclideanCLM (A q) v) i
    simpa [E, B, A, Matrix.mulVec, dotProduct] using h
  refine ⟨E, ?_, ?_⟩
  · intro q r hqr
    ext i
    fin_cases i
    · have h := congrArg (fun T : E3 →L[ℝ] E3 =>
          (T (EuclideanSpace.basisFun (Fin 3) ℝ 0)) 0) hqr
      rw [hE q, hE r] at h
      simpa [A, EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.single_apply] using h
    · have h := congrArg (fun T : E3 →L[ℝ] E3 =>
          (T (EuclideanSpace.basisFun (Fin 3) ℝ 1)) 1) hqr
      rw [hE q, hE r] at h
      simpa [A, EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.single_apply] using h
    · have h := congrArg (fun T : E3 →L[ℝ] E3 =>
          (T (EuclideanSpace.basisFun (Fin 3) ℝ 2)) 2) hqr
      rw [hE q, hE r] at h
      simpa [A, EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.single_apply] using h
    · have h := congrArg (fun T : E3 →L[ℝ] E3 =>
          (T (EuclideanSpace.basisFun (Fin 3) ℝ 1)) 0) hqr
      rw [hE q, hE r] at h
      simpa [A, EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.single_apply] using h
    · have h := congrArg (fun T : E3 →L[ℝ] E3 =>
          (T (EuclideanSpace.basisFun (Fin 3) ℝ 2)) 0) hqr
      rw [hE q, hE r] at h
      simpa [A, EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.single_apply] using h
    · have h := congrArg (fun T : E3 →L[ℝ] E3 =>
          (T (EuclideanSpace.basisFun (Fin 3) ℝ 2)) 1) hqr
      rw [hE q, hE r] at h
      simpa [A, EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.single_apply] using h
  · intro q v i
    simpa [A] using hE q v i
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
