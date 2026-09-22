import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
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
/-- Identify actual convolution derivatives, not only formal differentiated-kernel integrals. -/
theorem original_bounded_hessian_regression (f : E3 →ᵇ ℝ)
    {t : ℝ} (ht : 0 < t) :
    let u : E3 → ℝ := fun x => ∫ y : E3, euclideanHeatKernel 3 t (x-y)*f y
    ContDiff ℝ 2 u ∧ ∀ (x : E3) (i j : Fin 3),
      fderiv ℝ (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) =
      ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * f (x-y) :=
by
  exact euclideanHeatKernel_bounded_hessian_identification f ht
end MorganTianLib.ParabolicPDE
#print axioms MorganTianLib.ParabolicPDE.original_bounded_hessian_regression
