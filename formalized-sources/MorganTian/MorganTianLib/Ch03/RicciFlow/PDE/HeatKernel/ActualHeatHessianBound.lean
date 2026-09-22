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
/-- Holder smoothing bound for the ACTUAL second derivatives of convolution. -/
theorem actual_heat_hessian_holder_bound (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E3 →ᵇ ℝ) (L : ℝ), 0 ≤ L →
      (∀ x y : E3, |f x-f y| ≤ L*‖x-y‖^alpha) →
      ∀ t : ℝ, 0 < t →
        let u : E3 → ℝ := fun x => ∫ y : E3, euclideanHeatKernel 3 t (x-y)*f y
        ContDiff ℝ 2 u ∧ ∀ (x : E3) (i j : Fin 3),
          |fderiv ℝ (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single j 1)| ≤ C*L*t^(alpha/2-1) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, hbound⟩ :=
    euclideanHeatKernel_three_holder_hessian_convolution alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro f L hL hholder t ht
  obtain ⟨hu, hident⟩ := euclideanHeatKernel_bounded_hessian_identification f ht
  refine ⟨hu, ?_⟩
  intro x i j
  rw [hident x i j]
  exact (hbound f L hL hholder t ht i j x).2
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
