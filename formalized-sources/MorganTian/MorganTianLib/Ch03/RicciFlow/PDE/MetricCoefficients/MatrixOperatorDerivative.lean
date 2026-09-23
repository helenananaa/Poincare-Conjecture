import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Differentiate matrix-to-operator conversion entrywise. -/
theorem matrix_operator_fderiv (F : E3 → Matrix (Fin 3) (Fin 3) ℝ)
    (x v : E3) (hF : DifferentiableAt ℝ F x) :
    fderiv ℝ (fun y : E3 => Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (F y)) x v =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
        (fun i j : Fin 3 => fderiv ℝ (fun y : E3 => F y i j) x v) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : TopologicalSpace (Matrix (Fin 3) (Fin 3) ℝ) := Pi.topologicalSpace
  letI : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) := Pi.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) := Pi.normedSpace
  let L : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (E3 →L[ℝ] E3) :=
    LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
  have hL : HasFDerivAt (fun A : Matrix (Fin 3) (Fin 3) ℝ => L A) L (F x) :=
    L.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : E3 => L (F y))
      (L.comp (fderiv ℝ F x)) x := by
    exact HasFDerivAt.comp (x := x) (g := fun A : Matrix (Fin 3) (Fin 3) ℝ => L A)
      (g' := L) (f := F) (f' := fderiv ℝ F x) hL hF.hasFDerivAt
  have houter := fderiv_pi (fun i => differentiableAt_pi.1 hF i)
  have hrow (i : Fin 3) :=
    fderiv_pi (fun j => differentiableAt_pi.1 (differentiableAt_pi.1 hF i) j)
  calc
    fderiv ℝ (fun y : E3 => Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (F y)) x v
        = L (fderiv ℝ F x v) := by
          change (fderiv ℝ (fun y : E3 => L (F y)) x) v = _
          rw [hcomp.fderiv]
          rfl
    _ = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
        (fun i j : Fin 3 => fderiv ℝ (fun y : E3 => F y i j) x v) := by
          change Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (fderiv ℝ F x v) =
            Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
              (fun i j : Fin 3 => fderiv ℝ (fun y : E3 => F y i j) x v)
          apply congrArg (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ))
          ext i j
          have hv := congrArg (fun g : E3 →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ => g v) houter
          have hvi := congrArg (fun g : E3 →L[ℝ] (Fin 3 → ℝ) => g v) (hrow i)
          have hvij := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℝ => m i j) hv
          have hrij := congrArg (fun r : Fin 3 → ℝ => r j) hvi
          simpa using hvij.trans hrij
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
