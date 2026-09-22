import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveCompactSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveTimeExchange
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveLaplaceExchange
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Checked composition of the independent positive-time convolution leaves. -/
theorem euclideanHeatKernel_three_compact_classical_recursive (f : E3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    let u : ℝ → E3 → ℝ := fun t x => ∫ y : E3, euclideanHeatKernel 3 t (x-y) * f y
    (∀ t : ℝ, 0 < t → ∀ x : E3,
      Integrable (fun y : E3 => euclideanHeatKernel 3 t (x-y) * f y) volume) ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × E3 => u p.1 p.2) (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) ∧
    ∀ t : ℝ, 0 < t → ∀ x : E3,
      HasDerivAt (fun s => u s x) (∑ i : Fin 3, iteratedDeriv 2
        (fun z : ℝ => u t (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z))) (x i)) t :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  constructor
  · intro t ht x
    have hk : Continuous (euclideanHeatKernel 3 t) :=
      (euclideanHeatKernel_three_heat_equation ht).1.continuous
    have hcont : Continuous
        (fun y : E3 => euclideanHeatKernel 3 t (x - y) * f y) := by
      exact hk.comp (continuous_const.sub continuous_id) |>.mul hf.continuous
    exact hcont.integrable_of_hasCompactSupport hfc.mul_left
  constructor
  · exact euclideanHeatKernel_compact_convolution_smooth f hf hfc
  · intro t ht x
    have htime := euclideanHeatKernel_compact_time_derivative f hf hfc ht x
    have hlap := euclideanHeatKernel_compact_laplace_integral f hf hfc ht x
    have hkernel :
        (∫ y : E3, deriv (fun s => euclideanHeatKernel 3 s (x - y)) t * f y) =
          ∫ y : E3, (∑ i : Fin 3, iteratedDeriv 2 (fun z : ℝ =>
            euclideanHeatKernel 3 t
              (WithLp.toLp 2 (Function.update (WithLp.ofLp (x - y)) i z))) ((x - y) i)) * f y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        dsimp
        rw [(euclideanHeatKernel_three_heat_equation ht).2 (x - y)]
        simp only [WithLp.ofLp_sub, PiLp.sub_apply])
    have hcoeff :
        (∫ y : E3, deriv (fun s => euclideanHeatKernel 3 s (x - y)) t * f y) =
          ∑ i : Fin 3, iteratedDeriv 2 (fun z : ℝ =>
            ∫ y : E3, euclideanHeatKernel 3 t
              (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z) - y) * f y) (x i) := by
      rw [hkernel, ← hlap.2]
    convert htime.2 using 1
    exact hcoeff.symm
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
