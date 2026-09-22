import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatTimeEquation
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
/-- A classical C2-space, C1-time heat IVP with bounded uniformly continuous initial data. -/
theorem bounded_uniformly_continuous_heat_ivp (f : E3 →ᵇ ℝ) (hf : UniformContinuous f) :
    ∃ u : ℝ → E3 → ℝ, u 0 = f ∧
      (∀ t : ℝ, 0 < t → ∀ x : E3, u t x = ∫ y : E3, euclideanHeatKernel 3 t (x-y)*f y) ∧
      TendstoUniformly u f (𝓝[>] (0:ℝ)) ∧
      (∀ t : ℝ, 0 < t → ContDiff ℝ 2 (u t)) ∧
      ∀ t : ℝ, 0 < t → ∀ x : E3, HasDerivAt (fun s => u s x)
        (∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ (u t) z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let v : ℝ → E3 → ℝ := fun t x =>
    ∫ y : E3, euclideanHeatKernel 3 t (x - y) * f y
  let u : ℝ → E3 → ℝ := fun t x => if 0 < t then v t x else f x
  have hchange (t : ℝ) (ht : 0 < t) (x : E3) :
      (∫ y : E3, euclideanHeatKernel 3 t (x - y) * f y) =
        ∫ y : E3, euclideanHeatKernel 3 t y * f (x - y) := by
    have hmap := (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
      (MeasurableEquiv.subLeft x).measurableEmbedding
      (fun z : E3 => euclideanHeatKernel 3 t z * f (x - z))
    simpa [sub_sub_cancel] using hmap
  have htrace := euclideanHeatKernel_three_uniform_initial_trace f hf
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    simp [u]
  · intro t ht x
    simp [u, v, ht]
  · apply (tendstoUniformly_congr ?_).mp htrace
    filter_upwards [self_mem_nhdsWithin] with t ht
    funext x
    have ht' : 0 < t := ht
    rw [show u t x = v t x by
      dsimp [u]
      rw [if_pos ht']]
    exact (hchange t ht' x).symm
  · intro t ht
    have hv : ContDiff ℝ 2 (v t) := by
      simpa [v] using (euclideanHeatKernel_bounded_hessian_identification f ht).1
    simpa [u, ht] using hv
  · intro t ht x
    have hv := bounded_heat_time_equation f ht x
    have hder : HasDerivAt (fun s => v s x)
        (∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ (v t) z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) t := by
      simpa [v] using hv
    have huv : u t = v t := by
      funext z
      simp [u, ht]
    have hcoeff :
        (∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ (v t) z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) =
        ∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ (u t) z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := by
      rw [huv]
    have hev : (fun s => u s x) =ᶠ[𝓝 t] (fun s => v s x) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      have hs' : 0 < s := hs
      dsimp [u]
      rw [if_pos hs']
    have hu := hder.congr_of_eventuallyEq hev
    rw [hcoeff] at hu
    exact hu
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
