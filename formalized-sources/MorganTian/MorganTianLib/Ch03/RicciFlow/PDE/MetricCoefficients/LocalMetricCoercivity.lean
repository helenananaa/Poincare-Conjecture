import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PositivePerturbation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Pointwise coercivity persists locally for a continuous operator field. -/
theorem metric_coercive_eventually (G : E3 → (E3 →L[ℝ] E3))
    (x : E3) (hG : ContinuousAt G x) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ v : E3, c * ‖v‖ ^ 2 ≤ inner ℝ (G x v) v) :
    ∀ᶠ y : E3 in 𝓝 x, ∀ v : E3,
      (c / 2) * ‖v‖ ^ 2 ≤ inner ℝ (G y v) v :=
/- SWARM_PROOF_BEGIN -/
by
  have hcont : ContinuousAt (fun y : E3 => ‖G y - G x‖) x :=
    continuous_norm.continuousAt.comp (hG.sub continuousAt_const)
  have hsmall : ∀ᶠ y : E3 in 𝓝 x, ‖G y - G x‖ < c / 2 := by
    have hzero : ‖G x - G x‖ = 0 := by simp
    have hmem : ‖G x - G x‖ ∈ Set.Iio (c / 2) := by
      simpa [hzero] using (half_pos hc)
    exact hcont.eventually (Iio_mem_nhds hmem)
  filter_upwards [hsmall] with y hy
  exact coercivity_survives_operator_perturbation (G x) (G y) c hc hpos
    (le_of_lt hy)
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
