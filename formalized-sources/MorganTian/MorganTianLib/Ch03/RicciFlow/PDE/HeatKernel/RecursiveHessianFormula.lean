import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Exact coordinate Hessian entries of the actual three-dimensional Gaussian. -/
theorem euclideanHeatKernel_three_hessian_formula {t : ℝ} (ht : 0 < t)
    (x : E3) (i j : Fin 3) :
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
      (x i * x j / (4*t^2) - (if i=j then 1/(2*t) else 0)) * euclideanHeatKernel 3 t x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hgauss := gaussianHeatKernel_derivatives ht
  have hK : ContDiff ℝ ∞ (euclideanHeatKernel 3 t) :=
    (euclideanHeatKernel_three_heat_equation ht).1
  have hKdiff (z : E3) :
      DifferentiableAt ℝ (euclideanHeatKernel 3 t) z :=
    hK.differentiable (by simp) z
  have hfactor (k : Fin 3) (z : E3) :
      HasFDerivAt (fun y : E3 => gaussianHeatKernel t (y k))
        ((fderiv ℝ (gaussianHeatKernel t) (z k)).comp
          (PiLp.proj 2 (fun _ : Fin 3 => ℝ) k)) z := by
    simpa [Function.comp_def] using
      (hgauss.1.differentiable (by simp) (z k)).hasFDerivAt.comp z
        (PiLp.hasFDerivAt_apply 2 z k)
  have hfirst (z : E3) (i : Fin 3) :
      fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1) =
        -(z i / (2 * t)) * euclideanHeatKernel 3 t z := by
    have hfun : euclideanHeatKernel 3 t =
        (fun y : E3 => gaussianHeatKernel t (y 0) *
          (gaussianHeatKernel t (y 1) * gaussianHeatKernel t (y 2))) := by
      funext y
      simp [euclideanHeatKernel, Fin.prod_univ_succ]
    have hp := (hfactor 0 z).mul ((hfactor 1 z).mul (hfactor 2 z))
    rw [hfun]
    change fderiv ℝ
        ((fun y : E3 => gaussianHeatKernel t (y 0)) *
          ((fun y : E3 => gaussianHeatKernel t (y 1)) *
            (fun y : E3 => gaussianHeatKernel t (y 2)))) z
        (EuclideanSpace.single i 1) = _
    rw [hp.fderiv]
    fin_cases i <;> simp [hgauss.2, PiLp.proj_apply, EuclideanSpace.single_apply,
      fderiv_apply_one_eq_deriv] <;> ring
  have hfun (i : Fin 3) :
      (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) =
        (fun z : E3 => -(z i / (2 * t)) * euclideanHeatKernel 3 t z) := by
    funext z
    exact hfirst z i
  rw [hfun i]
  have hlin (z : E3) (i : Fin 3) :
      HasFDerivAt (fun y : E3 => -(y i / (2 * t)))
        ((-(1 / (2 * t)) : ℝ) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i)) z := by
    have hbase : HasFDerivAt (fun y : E3 => y i)
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) z :=
      PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z i
    have h := hbase.const_smul (-(1 / (2 * t)) : ℝ)
    have heq : (-(1 / (2 * t)) : ℝ) • (fun y : E3 => y i) =
        (fun y : E3 => -(y i / (2 * t))) := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq] at h
    exact h
  have hq := (hlin x i).mul (hKdiff x).hasFDerivAt
  change fderiv ℝ
      ((fun y : E3 => -(y i / (2 * t))) * (euclideanHeatKernel 3 t)) x
      (EuclideanSpace.single j 1) = _
  rw [hq.fderiv]
  fin_cases i <;> fin_cases j <;>
    simp [hfirst, PiLp.proj_apply, EuclideanSpace.single_apply,
      fderiv_apply_one_eq_deriv] <;> ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
