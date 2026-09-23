import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianHessianTimeDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.DuhamelPastIntegrability
open MorganTianLib.MetricCoefficient Set MeasureTheory
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** The actual Duhamel Hessian integrand is integrable on every initial subinterval. -/
theorem duhamel_hessian_initial_interval_integrable
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (F : (ℝ × E3) →ᵇ ℝ) (L T t : ℝ) (hL : 0 ≤ L)
    (hT : 0 ≤ T) (ht : 0 ≤ t) (htT : t ≤ T)
    (hholder : ∀ s ∈ Icc (0:ℝ) T, ∀ x z : E3,
      |F (s,x)-F (s,z)| ≤ L*‖x-z‖^alpha) (x : E3) (i j : Fin 3) :
    IntervalIntegrable (fun s => ∫ y : E3,
      heatHessian3 (T-s) i j y * F (s,x-y)) volume 0 t :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hCpos, hcontrol⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_duhamel_hessian_control
      alpha ha ha1
  have hFbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ y : E3, |F (s, y)| ≤ ‖F‖ := by
    intro s hs y
    simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s, y)
  have hfull := hcontrol F F.continuous ‖F‖ L T (norm_nonneg _) hL hT
    hFbound hholder i j x
  apply hfull.1.mono_set
  rw [Set.uIcc_of_le ht, Set.uIcc_of_le hT]
  intro s hs
  exact ⟨hs.1, le_trans hs.2 htT⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.DuhamelPastIntegrability
