import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHolderControl
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual first coordinate derivative, needed independently of the Hessian theorem. -/
theorem euclideanHeatKernel_three_gradient_formula {t : ℝ} (ht : 0 < t)
    (x : E3) (i : Fin 3) : fderiv ℝ (euclideanHeatKernel 3 t) x (EuclideanSpace.single i 1) =
      -(x i/(2*t))*euclideanHeatKernel 3 t x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hgauss := gaussianHeatKernel_derivatives ht
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
  exact hfirst x i
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
