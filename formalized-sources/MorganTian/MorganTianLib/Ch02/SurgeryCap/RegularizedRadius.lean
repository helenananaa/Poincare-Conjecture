import MorganTianLib.Ch02.SurgeryCap.RadialControl
open Riemannian
open scoped Manifold ContDiff RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** A globally smooth approximation to the radial coordinate. -/
theorem regularizedRadius_contDiff (e : ℝ) (he : 0 < e) :
    ContDiff ℝ ∞ (fun x : E3 => Real.sqrt (‖x‖^2 + e^2)) := by
  apply ((contDiff_norm_sq ℝ).add contDiff_const).sqrt
  intro x
  exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos he))

/-- **Math.** The differential is the normalized Euclidean radial covector. -/
theorem regularizedRadius_fderiv (e : ℝ) (he : 0 < e) (x v : E3) :
    fderiv ℝ (fun y : E3 => Real.sqrt (‖y‖^2 + e^2)) x v =
      inner ℝ x v / Real.sqrt (‖x‖^2 + e^2) := by
  have hd : 0 < ‖x‖^2 + e^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos he)
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (e^2)).sqrt hd.ne'
  rw [h.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, two_smul, add_apply]
  field_simp
  <;> ring

/-- **Math.** The actual differential is bounded by the constructed cap speed. -/
theorem RoundCapProfile.regularizedRadius_differential_bound
    (P : RoundCapProfile) (e : ℝ) (he : 0 < e) (x v : E3) :
    |fderiv ℝ (fun y : E3 => Real.sqrt (‖y‖^2 + e^2)) x v| ≤
      Real.sqrt (P.globalMetric.metricInner x v v) := by
  rw [regularizedRadius_fderiv e he x v]
  exact P.globalMetric_regularized_radial_bound e he x v

end MorganTianLib.SurgeryCap
