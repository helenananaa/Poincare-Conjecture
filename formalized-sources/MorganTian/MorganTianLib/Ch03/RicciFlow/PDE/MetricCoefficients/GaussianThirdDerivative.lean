import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)
def heatHessian3 (t : ℝ) (i j : Fin 3) (x : E3) : ℝ :=
  fderiv ℝ (fun z : E3 => fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t) z
    (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)

/-- **Math.** gaussian third derivative. -/
theorem gaussian_third_derivative 
    {t : ℝ} (ht : 0 < t) (x : E3) (i j k : Fin 3) :
    fderiv ℝ (heatHessian3 t i j) x (EuclideanSpace.single k 1) =
      (((if i=j then x k else 0)+(if i=k then x j else 0)+(if j=k then x i else 0))/(4*t^2) -
        x i*x j*x k/(8*t^3))*MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : E3 → ℝ := MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t
  let c : ℝ := 1 / (4 * t^2)
  let d : ℝ := if i = j then 1 / (2 * t) else 0
  let A : E3 → ℝ := (fun y : E3 => c * (y i * y j)) - (fun _ : E3 => d)
  have hH : heatHessian3 t i j = fun y => A y * K y := by
    funext y
    dsimp [heatHessian3, A, c, d, K]
    rw [MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_hessian_formula ht y i j]
    congr 1
    field_simp [ne_of_gt ht]
  rw [hH]
  have hi : HasFDerivAt (fun y : E3 => y i)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) x :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x i
  have hj : HasFDerivAt (fun y : E3 => y j)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) x :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x j
  have hbase := (hi.mul hj).const_mul c
  have hA : HasFDerivAt A
      (c • ((x i) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j +
        (x j) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) - 0) x := by
    change HasFDerivAt ((fun y : E3 => c * (y i * y j)) - (fun _ : E3 => d)) _ x
    exact hbase.sub (hasFDerivAt_const d x)
  have hKdiff := (MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_heat_equation ht).1.differentiable
    (by simp) x
  have hK : HasFDerivAt K (fderiv ℝ K x) x := hKdiff.hasFDerivAt
  have hprod := hA.mul hK
  change fderiv ℝ (A * K) x (EuclideanSpace.single k 1) = _
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply]
  dsimp only [K]
  rw [MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_gradient_formula ht x k]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [A, c, d, PiLp.proj_apply] <;>
    field_simp [ne_of_gt ht] <;> ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
