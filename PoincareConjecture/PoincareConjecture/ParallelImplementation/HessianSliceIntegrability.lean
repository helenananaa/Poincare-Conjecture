import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianHessianTimeDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianCancellationThree
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.HessianSliceIntegrability
open MorganTianLib.MetricCoefficient Set MeasureTheory
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** A bounded time slice multiplied by an actual positive-time heat Hessian is integrable. -/
theorem heatHessian_time_slice_integrable (F : (ℝ × E3) →ᵇ ℝ)
    (r s : ℝ) (hr : 0 < r) (x : E3) (i j : Fin 3) :
    Integrable (fun y : E3 => heatHessian3 r i j y * F (s, x-y)) volume :=
/- SWARM_PROOF_BEGIN -/
by
  have hkernel : Integrable (fun y : E3 => heatHessian3 r i j y) volume := by
    simpa [heatHessian3] using
      (MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_hessian_cancellation hr i j).1
  have hslice : Continuous (fun y : E3 => F (s, x - y)) := by
    exact F.continuous.comp
      (continuous_const.prodMk (continuous_const.sub continuous_id))
  have hmul := hkernel.mul_bdd hslice.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => F.norm_coe_le_norm (s, x - y))
  simpa using hmul
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.HessianSliceIntegrability
