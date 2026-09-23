import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianTemporalDerivativeBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.TemporalHessianPointwise
open MorganTianLib.MetricCoefficient
open Set MeasureTheory
open scoped Topology
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Actual heat Hessian time differences are controlled by its derivative envelope. -/
theorem heatHessian_time_difference_pointwise
    (alpha t h : ℝ) (ha : 0 < alpha) (ht : 0 < t)
    (hh : 0 ≤ h) (hht : h ≤ t) (y : E3) (i j : Fin 3) :
    |heatHessian3 (t+h) i j y - heatHessian3 t i j y| * ‖y‖^alpha ≤
      h * temporalGaussianEnvelope alpha t y :=
/- SWARM_PROOF_BEGIN -/
by
  by_cases hh0 : h = 0
  · simp [hh0]
  let w : ℝ := ‖y‖ ^ alpha
  let f : ℝ → ℝ := fun r => heatHessian3 r i j y * w
  have hw : 0 ≤ w := by
    exact Real.rpow_nonneg (norm_nonneg y) alpha
  have hderiv (r : ℝ) (hr : t ≤ r) :
      HasDerivAt f (deriv (fun s => heatHessian3 s i j y) r * w) r := by
    have hrpos : 0 < r := lt_of_lt_of_le ht hr
    have hd := gaussian_hessian_time_derivative r hrpos y i j
    have hmul := hd.mul_const w
    simpa [f, hd.deriv] using hmul
  have hdiff : DifferentiableOn ℝ f (Icc t (t + h)) := by
    intro r hr
    exact (hderiv r hr.1).differentiableAt.differentiableWithinAt
  have hbound : ∀ r ∈ Ico t (t + h),
      ‖deriv (fun s => heatHessian3 s i j y) r * w‖ ≤
        temporalGaussianEnvelope alpha t y := by
    intro r hr
    have hr2 : r ≤ 2 * t := by linarith [hr.2, hht]
    have hb := gaussian_temporal_derivative_bound alpha t r ha ht hr.1 hr2 y i j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    simpa [w] using hb
  have hmv : ‖f (t + h) - f t‖ ≤
      temporalGaussianEnvelope alpha t y * ((t + h) - t) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (a := t) (b := t + h)
      (f' := fun r => deriv (fun s => heatHessian3 s i j y) r * w)
      (C := temporalGaussianEnvelope alpha t y)
      (fun r hr => (hderiv r hr.1).hasDerivWithinAt)
      hbound (t + h) ⟨by linarith [hh], le_rfl⟩
  have hform : ‖f (t + h) - f t‖ =
      |heatHessian3 (t + h) i j y - heatHessian3 t i j y| * ‖y‖ ^ alpha := by
    simp only [f, Real.norm_eq_abs]
    rw [show heatHessian3 (t + h) i j y * w - heatHessian3 t i j y * w =
      (heatHessian3 (t + h) i j y - heatHessian3 t i j y) * w by ring]
    rw [abs_mul, abs_of_nonneg hw]
  rw [hform] at hmv
  calc
    |heatHessian3 (t + h) i j y - heatHessian3 t i j y| * ‖y‖ ^ alpha ≤
        temporalGaussianEnvelope alpha t y * ((t + h) - t) := hmv
    _ = h * temporalGaussianEnvelope alpha t y := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.TemporalHessianPointwise
