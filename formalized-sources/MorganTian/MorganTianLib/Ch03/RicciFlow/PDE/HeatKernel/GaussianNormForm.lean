import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideHessianUnweighted
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual product kernel in radial Euclidean coordinates. -/
theorem euclideanHeatKernel_three_norm_form (t : ℝ) (x : E3) :
    euclideanHeatKernel 3 t x =
      (Real.sqrt (4 * Real.pi * t))⁻¹ ^ (3 : ℕ) * Real.exp (-‖x‖^2/(4*t)) :=
/- SWARM_PROOF_BEGIN -/
by
  unfold euclideanHeatKernel gaussianHeatKernel
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  simp only [Finset.prod_const]
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 2
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
