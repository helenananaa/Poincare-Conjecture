import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseQuadraticRemainder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PrincipalPartDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Realization of coefficient-array contraction as an actual continuous bilinear map. -/
theorem principal_contraction_bilinear :
    ∃ B : (E3 →L[ℝ] E3) →L[ℝ] ((Fin 3 → Fin 3 → E6) →L[ℝ] E6),
      ∀ (A : E3 →L[ℝ] E3) (Q : Fin 3 → Fin 3 → E6),
      B A Q = ∑ i : Fin 3, ∑ j : Fin 3, (A (EuclideanSpace.single j 1)) i • Q i j :=
/- SWARM_PROOF_BEGIN -/
by
  let c : Fin 3 → Fin 3 → (E3 →L[ℝ] E3) →L[ℝ] ℝ := fun i j =>
    (EuclideanSpace.proj i).comp
      ((ContinuousLinearMap.apply ℝ E3) (EuclideanSpace.single j 1))
  let p : Fin 3 → Fin 3 → (Fin 3 → Fin 3 → E6) →L[ℝ] E6 := fun i j =>
    (ContinuousLinearMap.proj (R := ℝ) j : (Fin 3 → E6) →L[ℝ] E6).comp
      (ContinuousLinearMap.proj (R := ℝ) i :
        (Fin 3 → Fin 3 → E6) →L[ℝ] (Fin 3 → E6))
  let B : (E3 →L[ℝ] E3) →L[ℝ] ((Fin 3 → Fin 3 → E6) →L[ℝ] E6) :=
    ∑ i : Fin 3, ∑ j : Fin 3,
      (ContinuousLinearMap.smulRightL ℝ (E3 →L[ℝ] E3)
        ((Fin 3 → Fin 3 → E6) →L[ℝ] E6)) (c i j) (p i j)
  refine ⟨B, ?_⟩
  intro A Q
  simp [B, c, p, ContinuousLinearMap.smulRight_apply]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
