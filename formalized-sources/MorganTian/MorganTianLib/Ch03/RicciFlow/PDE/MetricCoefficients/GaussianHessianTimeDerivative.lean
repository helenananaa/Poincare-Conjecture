import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianThirdDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ActualHeatTimeFormula
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** gaussian hessian time derivative. -/
theorem gaussian_hessian_time_derivative 
    (t : ℝ) (ht : 0 < t) (y : E3) (i j : Fin 3) :
    HasDerivAt (fun r : ℝ => heatHessian3 r i j y)
      ((-(y i*y j)/(2*t^3) + (if i=j then 1/(2*t^2) else 0) +
        (y i*y j/(4*t^2)-(if i=j then 1/(2*t) else 0)) *
          (‖y‖^2/(4*t^2)-3/(2*t))) *
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t y) t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : ℝ → ℝ := fun r =>
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 r y
  let A : ℝ → ℝ := fun r =>
    y i * y j / (4 * r^2) - (if i = j then 1 / (2 * r) else 0)
  have hformula : (fun r : ℝ => heatHessian3 r i j y) =ᶠ[𝓝 t]
      (fun r => A r * K r) := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    dsimp [heatHessian3, A, K]
    rw [MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_hessian_formula
      hr y i j]
  let a : ℝ := y i * y j / 4
  let b : ℝ := if i = j then 1 / 2 else 0
  have hinv : HasDerivAt (fun r : ℝ => r⁻¹) (-(t ^ 2)⁻¹) t :=
    hasDerivAt_inv (ne_of_gt ht)
  have hsq : HasDerivAt (fun r : ℝ => r⁻¹ * r⁻¹)
      ((-(t ^ 2)⁻¹) * t⁻¹ + t⁻¹ * (-(t ^ 2)⁻¹)) t :=
    hinv.mul hinv
  have hcoef : HasDerivAt
      (fun r : ℝ => a * (r⁻¹ * r⁻¹) - b * r⁻¹)
      (a * ((-(t ^ 2)⁻¹) * t⁻¹ + t⁻¹ * (-(t ^ 2)⁻¹)) -
        b * (-(t ^ 2)⁻¹)) t := by
    exact (hsq.const_mul a).sub (hinv.const_mul b)
  have hAeq : (fun r : ℝ => a * (r⁻¹ * r⁻¹) - b * r⁻¹) =ᶠ[𝓝 t] A := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    change 0 < r at hr
    dsimp [A, a, b]
    field_simp [ne_of_gt hr]
    by_cases hij : i = j
    · simp [hij]
      field_simp [ne_of_gt hr]
    · simp [hij]
  have hApre : HasDerivAt A
      (a * ((-(t ^ 2)⁻¹) * t⁻¹ + t⁻¹ * (-(t ^ 2)⁻¹)) -
        b * (-(t ^ 2)⁻¹)) t :=
    hcoef.congr_of_eventuallyEq hAeq.symm
  have hA : HasDerivAt A
      (-(y i * y j) / (2 * t^3) +
        (if i = j then 1 / (2 * t^2) else 0)) t := by
    convert hApre using 1
    dsimp [a, b]
    by_cases hij : i = j <;> simp [hij] <;>
      field_simp [ne_of_gt ht] <;> ring
  have hK : HasDerivAt K
      ((‖y‖^2 / (4 * t^2) - 3 / (2 * t)) * K t) t := by
    simpa [K] using
      (MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_time_formula ht y)
  have hprod := hA.mul hK
  have hresult := hprod.congr_of_eventuallyEq hformula
  apply hresult.congr_deriv
  simp only [A, K]
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
