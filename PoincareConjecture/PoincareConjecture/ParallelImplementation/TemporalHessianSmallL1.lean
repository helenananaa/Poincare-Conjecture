import PoincareConjecture.ParallelImplementation.TemporalHessianPointwise
import PoincareConjecture.ParallelImplementation.TemporalHessianCoarse
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.TemporalGaussianEnvelope
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.TemporalHessianSmallL1
open MorganTianLib.MetricCoefficient
open Set MeasureTheory
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Integrated small-time-difference bound for the actual heat Hessian. -/
theorem heatHessian_time_difference_small_L1
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t h : ℝ, 0 < t → 0 ≤ h → h ≤ t → ∀ i j : Fin 3,
      (∫ y : E3, |heatHessian3 (t+h) i j y - heatHessian3 t i j y| * ‖y‖^alpha) ≤
        C * h * t^(alpha/2-2) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨_, _, hcoarse⟩ :=
    PoincareConjecture.ParallelImplementation.TemporalHessianCoarse.heatHessian_time_difference_coarse
      alpha ha ha1
  obtain ⟨C, hC, henvelope⟩ := temporal_gaussian_envelope_integral alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro t h ht hh hht i j
  obtain ⟨hI, _⟩ := hcoarse t h ht hh i j
  obtain ⟨hEnvI, _, hEnvBound⟩ := henvelope t ht
  have hpoint (y : E3) :
      |heatHessian3 (t + h) i j y - heatHessian3 t i j y| * ‖y‖ ^ alpha ≤
        h * temporalGaussianEnvelope alpha t y := by
    exact PoincareConjecture.ParallelImplementation.TemporalHessianPointwise.heatHessian_time_difference_pointwise
      alpha t h ha ht hh hht y i j
  calc
    (∫ y : E3, |heatHessian3 (t + h) i j y - heatHessian3 t i j y| * ‖y‖ ^ alpha) ≤
        ∫ y : E3, h * temporalGaussianEnvelope alpha t y ∂volume :=
      integral_mono hI (hEnvI.const_mul h) hpoint
    _ = h * ∫ y : E3, temporalGaussianEnvelope alpha t y ∂volume := by
      rw [integral_const_mul]
    _ ≤ h * (C * t ^ (alpha / 2 - 2)) :=
      mul_le_mul_of_nonneg_left hEnvBound hh
    _ = C * h * t ^ (alpha / 2 - 2) := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.TemporalHessianSmallL1
