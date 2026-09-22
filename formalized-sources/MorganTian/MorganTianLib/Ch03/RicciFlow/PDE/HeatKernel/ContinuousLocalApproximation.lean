import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HistoryHessianJointContinuity
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideDuhamelHessianThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatGeneratorC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildRestart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- A pointwise function is continuous if arbitrarily close continuous local approximants exist. -/
theorem continuousAt_of_local_approximants {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X)
    (h : ∀ eps : ℝ, 0<eps → ∃ g : X → ℝ,
      ContinuousAt g x ∧ ∀ᶠ y in 𝓝 x, |f y-g y|≤eps) : ContinuousAt f x :=
/- SWARM_PROOF_BEGIN -/
by
  refine Metric.continuousAt_iff'.2 fun eps heps => ?_
  obtain ⟨g, hg, hfg⟩ := h (eps / 3) (by linarith)
  have hgy : ∀ᶠ y in 𝓝 x, dist (g y) (g x) < eps / 3 :=
    (Metric.continuousAt_iff'.1 hg) (eps / 3) (by linarith)
  have hfgx : x ∈ {y : X | |f y - g y| ≤ eps / 3} := mem_of_mem_nhds hfg
  have hfgx' : |g x - f x| ≤ eps / 3 := by
    simpa [abs_sub_comm] using hfgx
  filter_upwards [hfg, hgy] with y hy hgy
  rw [Real.dist_eq] at hgy ⊢
  calc
    |f y - f x| ≤ |f y - g y| + |g y - g x| + |g x - f x| := by
      rw [show f y - f x = (f y - g y) + (g y - g x) + (g x - f x) by ring]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < eps / 3 + eps / 3 + eps / 3 := by
      linarith
    _ = eps := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
