import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianEstimate
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideHessianUnweighted
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatTimeDerivativeL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalInitialTrace
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ShiftedDerivativeDominator
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual positive-time derivative in radial coordinates. -/
theorem euclideanHeatKernel_three_time_formula {t : ℝ} (ht : 0 < t) (y : E3) :
    HasDerivAt (fun s => euclideanHeatKernel 3 s y)
      ((‖y‖^2/(4*t^2) - 3/(2*t))*euclideanHeatKernel 3 t y) t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hgauss := gaussianHeatKernel_derivatives ht
  have htime_ne : t ≠ 0 := ne_of_gt ht
  have htime_pos : 0 < 4 * Real.pi * t := by positivity
  have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi * t) :=
    Real.sqrt_pos.2 htime_pos
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := ne_of_gt hsqrt_pos
  have htimeDiff (x : ℝ) :
      DifferentiableAt ℝ (fun s : ℝ => gaussianHeatKernel s x) t := by
    have hargDiff : DifferentiableAt ℝ (fun s : ℝ => 4 * Real.pi * s) t := by
      fun_prop
    have hsqrtDiff : DifferentiableAt ℝ (fun s : ℝ =>
        Real.sqrt (4 * Real.pi * s)) t :=
      hargDiff.sqrt htime_pos.ne'
    have hnormDiff : DifferentiableAt ℝ (fun s : ℝ =>
        (Real.sqrt (4 * Real.pi * s))⁻¹) t :=
      hsqrtDiff.inv hsqrt_ne
    have hEtimeDiff : DifferentiableAt ℝ
        (fun s : ℝ => -(x ^ 2) / (4 * s)) t := by
      have hinv : DifferentiableAt ℝ (fun s : ℝ => s⁻¹) t :=
        differentiableAt_inv_iff.mpr htime_ne
      have htmp := hinv.const_mul (-(x ^ 2) / 4)
      exact htmp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by ring))
    unfold gaussianHeatKernel
    exact hnormDiff.mul
      (Real.differentiableAt_exp.comp t hEtimeDiff)
  have htimeFactor (x : ℝ) :
      HasDerivAt (fun s : ℝ => gaussianHeatKernel s x)
        (gaussianHeatHessian t x) t := by
    exact (htimeDiff x).hasDerivAt.congr_deriv (hgauss.2 x).2.2
  have htime :
      HasDerivAt (fun s : ℝ => ∏ i : Fin 3, gaussianHeatKernel s (y i))
        (∑ i : Fin 3,
          (∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (y j)) *
            gaussianHeatHessian t (y i)) t := by
    exact HasDerivAt.finsetProd (u := Finset.univ)
      (f := fun i : Fin 3 => fun s : ℝ => gaussianHeatKernel s (y i))
      (f' := fun i : Fin 3 => gaussianHeatHessian t (y i))
      (fun i _ => htimeFactor (y i))
  have hfull (i : Fin 3) :
      gaussianHeatKernel t (y i) *
          ∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (y j) =
        euclideanHeatKernel 3 t y := by
    unfold euclideanHeatKernel
    rw [Finset.mul_prod_erase Finset.univ
      (fun j : Fin 3 => gaussianHeatKernel t (y j)) (Finset.mem_univ i)]
  have hvalue :
      (∑ i : Fin 3,
        (∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (y j)) *
          gaussianHeatHessian t (y i)) =
        (‖y‖^2/(4*t^2) - 3/(2*t)) * euclideanHeatKernel 3 t y := by
    unfold gaussianHeatHessian
    calc
      (∑ i : Fin 3,
          ((∏ j ∈ (Finset.univ.erase i), gaussianHeatKernel t (y j)) *
            (((y i)^2/(4*t^2) - 1/(2*t)) * gaussianHeatKernel t (y i)))) =
          ∑ i : Fin 3, ((y i)^2/(4*t^2) - 1/(2*t)) *
            euclideanHeatKernel 3 t y := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [← hfull i]
              ring
      _ = (‖y‖^2/(4*t^2) - 3/(2*t)) * euclideanHeatKernel 3 t y := by
        rw [EuclideanSpace.real_norm_sq_eq]
        rw [← Finset.sum_mul]
        have hcoeff :
            (∑ i : Fin 3, ((y i)^2/(4*t^2) - 1/(2*t))) =
              (∑ i : Fin 3, (y i)^2)/(4*t^2) - 3/(2*t) := by
          rw [Finset.sum_sub_distrib, Finset.sum_div]
          have hconst : (∑ i : Fin 3, (1 : ℝ)/(2*t)) = 3/(2*t) := by
            simp
            ring
          rw [hconst]
        rw [hcoeff]
  convert htime using 1
  · simp only [euclideanHeatKernel]
  · exact hvalue.symm
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
