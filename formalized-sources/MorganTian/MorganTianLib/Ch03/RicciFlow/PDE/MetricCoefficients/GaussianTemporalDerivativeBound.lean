import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianHessianTimeDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianComparableTimes
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.TemporalGaussianEnvelope
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** gaussian temporal derivative bound. -/
theorem gaussian_temporal_derivative_bound 
    (alpha t r : ℝ) (ha : 0 < alpha) (ht : 0 < t) (htr : t ≤ r) (hrt : r ≤ 2*t)
    (y : E3) (i j : Fin 3) :
    |deriv (fun s : ℝ => heatHessian3 s i j y) r| * ‖y‖^alpha ≤
      temporalGaussianEnvelope alpha t y :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  by_cases hy : y = 0
  · subst y
    have ha2 : alpha + 2 ≠ 0 := by linarith
    have ha4 : alpha + 4 ≠ 0 := by linarith
    simp [temporalGaussianEnvelope, Real.zero_rpow, ha.ne', ha2, ha4]
  · have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    let q : ℝ := ‖y‖ ^ 2
    let P : ℝ :=
      -(y i * y j) / (2 * r^3) + (if i = j then 1 / (2 * r^2) else 0) +
        (y i * y j / (4 * r^2) - (if i = j then 1 / (2 * r) else 0)) *
          (‖y‖^2 / (4 * r^2) - 3 / (2 * r))
    let K : ℝ := MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 r y
    let K₂ : ℝ := MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2*t) y
    have hr : 0 < r := lt_of_lt_of_le ht htr
    have hK : 0 ≤ K := by
      dsimp [K]
      exact (MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos 3 hr y).le
    have hK₂ : 0 ≤ K₂ := by
      dsimp [K₂]
      exact (MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos 3 (by positivity) y).le
    have hkernel := gaussian_comparable_times t r ht htr hrt y
    have hformula := gaussian_hessian_time_derivative r hr y i j
    have hderiv : deriv (fun s : ℝ => heatHessian3 s i j y) r = P * K := by
      dsimp [P, K]
      exact hformula.deriv
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hyi : |y i| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y i)
    have hyj : |y j| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y j)
    have hprod : |y i * y j| ≤ q := by
      rw [abs_mul]
      dsimp [q]
      exact (mul_le_mul hyi hyj (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)
    have hr2 : 0 < 4 * r^2 := by positivity
    have hr3 : 0 < 2 * r^3 := by positivity
    have hr1 : 0 < 2 * r := by positivity
    have hfirst : |-(y i * y j) / (2 * r^3)| ≤ q / (2 * r^3) := by
      rw [abs_div, abs_neg, abs_of_pos hr3]
      exact div_le_div_of_nonneg_right hprod hr3.le
    have hdiag2 : |(if i = j then 1 / (2 * r^2) else 0)| ≤ 1 / (2 * r^2) := by
      by_cases hij : i = j
      · rw [if_pos hij, abs_of_pos (by positivity : 0 < (1 : ℝ) / (2 * r^2))]
      · rw [if_neg hij, abs_zero]
        positivity
    have hdiag1 : |(if i = j then 1 / (2 * r) else 0)| ≤ 1 / (2 * r) := by
      by_cases hij : i = j
      · rw [if_pos hij, abs_of_pos (by positivity : 0 < (1 : ℝ) / (2 * r))]
      · rw [if_neg hij, abs_zero]
        positivity
    have hcoef :
        |y i * y j / (4 * r^2) - (if i = j then 1 / (2 * r) else 0)| ≤
          q / (4 * r^2) + 1 / (2 * r) := by
      calc
        _ ≤ |y i * y j / (4 * r^2)| +
              |(if i = j then 1 / (2 * r) else 0)| := by
          simpa [abs_neg] using
            (abs_sub_le (y i * y j / (4 * r^2)) (0 : ℝ)
              (if i = j then 1 / (2 * r) else 0))
        _ = |y i * y j| / (4 * r^2) +
              |(if i = j then 1 / (2 * r) else 0)| := by
          rw [abs_div, abs_of_pos hr2]
        _ ≤ q / (4 * r^2) + 1 / (2 * r) := by
          exact add_le_add (div_le_div_of_nonneg_right hprod hr2.le) hdiag1
    have hfactor :
        |‖y‖^2 / (4 * r^2) - 3 / (2 * r)| ≤
          q / (4 * r^2) + 3 / (2 * r) := by
      change |‖y‖^2 / (4 * r^2) - 3 / (2 * r)| ≤
        ‖y‖^2 / (4 * r^2) + 3 / (2 * r)
      calc
        _ ≤ |‖y‖^2 / (4 * r^2)| + |3 / (2 * r)| := by
          simpa [abs_neg] using
            (abs_sub_le (‖y‖^2 / (4 * r^2)) (0 : ℝ) (3 / (2 * r)))
        _ = ‖y‖^2 / (4 * r^2) + 3 / (2 * r) := by
          simp [abs_div, abs_of_pos hr2, abs_of_nonneg (sq_nonneg ‖y‖),
            abs_of_pos (by positivity : 0 < 2 * r)]
    have htail :
        |(y i * y j / (4 * r^2) - (if i = j then 1 / (2 * r) else 0)) *
            (‖y‖^2 / (4 * r^2) - 3 / (2 * r))| ≤
          (q / (4 * r^2) + 1 / (2 * r)) *
            (q / (4 * r^2) + 3 / (2 * r)) := by
      rw [abs_mul]
      exact mul_le_mul hcoef hfactor (abs_nonneg _) (by positivity)
    have hpoly : |P| ≤ q^2 / (16 * r^4) + q / r^3 + 5 / (4 * r^2) := by
      dsimp [P]
      calc
        |-(y i * y j) / (2 * r^3) +
            (if i = j then 1 / (2 * r^2) else 0) +
            (y i * y j / (4 * r^2) - (if i = j then 1 / (2 * r) else 0)) *
              (‖y‖^2 / (4 * r^2) - 3 / (2 * r))|
            ≤ |-(y i * y j) / (2 * r^3)| +
              |(if i = j then 1 / (2 * r^2) else 0)| +
              |(y i * y j / (4 * r^2) - (if i = j then 1 / (2 * r) else 0)) *
                (‖y‖^2 / (4 * r^2) - 3 / (2 * r))| := by
          calc
            _ ≤ |-(y i * y j) / (2 * r^3) +
                  (if i = j then 1 / (2 * r^2) else 0)| +
                |(y i * y j / (4 * r^2) - (if i = j then 1 / (2 * r) else 0)) *
                  (‖y‖^2 / (4 * r^2) - 3 / (2 * r))| := abs_add_le _ _
            _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
        _ ≤ q / (2 * r^3) + 1 / (2 * r^2) +
              (q / (4 * r^2) + 1 / (2 * r)) *
                (q / (4 * r^2) + 3 / (2 * r)) := by
          exact add_le_add (add_le_add hfirst hdiag2) htail
        _ = q^2 / (16 * r^4) + q / r^3 + 5 / (4 * r^2) := by
          ring
    have hrpow (n : ℕ) : t^n ≤ r^n := pow_le_pow_left₀ ht.le htr n
    have hred :
        q^2 / (16 * r^4) + q / r^3 + 5 / (4 * r^2) ≤
          q^2 / (16 * t^4) + q / t^3 + 5 / (4 * t^2) := by
      have h₄ : q^2 / (16 * r^4) ≤ q^2 / (16 * t^4) := by
        apply div_le_div_of_nonneg_left (sq_nonneg q) (by positivity)
        nlinarith [hrpow 4]
      have h₃ : q / r^3 ≤ q / t^3 := by
        apply div_le_div_of_nonneg_left hq (by positivity)
        nlinarith [hrpow 3]
      have h₂ : 5 / (4 * r^2) ≤ 5 / (4 * t^2) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [hrpow 2]
      exact add_le_add (add_le_add h₄ h₃) h₂
    let B : ℝ := q^2 / (16 * t^4) + q / t^3 + 5 / (4 * t^2)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hnα : 0 ≤ ‖y‖^alpha := Real.rpow_nonneg (norm_nonneg y) alpha
    have hcoeff :
        8 * B * ‖y‖^alpha ≤
          64 * (‖y‖^alpha / t^2 + ‖y‖^(alpha+2) / t^3 +
            ‖y‖^(alpha+4) / t^4) := by
      have hp2 : ‖y‖^(alpha+2) = ‖y‖^alpha * q := by
        rw [Real.rpow_add hn alpha 2]
        dsimp [q]
        exact congrArg (fun z : ℝ => ‖y‖^alpha * z)
          (Real.rpow_natCast ‖y‖ 2)
      have hp4 : ‖y‖^(alpha+4) = ‖y‖^alpha * q^2 := by
        rw [Real.rpow_add hn alpha 4]
        dsimp [q]
        calc
          ‖y‖^alpha * ‖y‖^(4 : ℝ) = ‖y‖^alpha * ‖y‖^4 :=
            congrArg (fun z : ℝ => ‖y‖^alpha * z) (Real.rpow_natCast ‖y‖ 4)
          _ = ‖y‖^alpha * (‖y‖^2)^2 := by ring
      rw [hp2, hp4]
      dsimp [B]
      have h0 : 0 ≤ ‖y‖^alpha / t^2 := by positivity
      have h1 : 0 ≤ (‖y‖^alpha * q) / t^3 := by positivity
      have h2 : 0 ≤ (‖y‖^alpha * q^2) / t^4 := by positivity
      calc
        8 * (q^2 / (16 * t^4) + q / t^3 + 5 / (4 * t^2)) * ‖y‖^alpha =
            10 * (‖y‖^alpha / t^2) +
              8 * ((‖y‖^alpha * q) / t^3) +
              (1 / 2) * ((‖y‖^alpha * q^2) / t^4) := by
          field_simp [ne_of_gt ht]; ring
        _ ≤ 64 * (‖y‖^alpha / t^2 +
              (‖y‖^alpha * q) / t^3 +
              (‖y‖^alpha * q^2) / t^4) := by
          nlinarith [h0, h1, h2]
    have hpoint :
        |deriv (fun s : ℝ => heatHessian3 s i j y) r| * ‖y‖^alpha ≤
          temporalGaussianEnvelope alpha t y := by
      have hpoly_nonneg :
          0 ≤ q^2 / (16 * r^4) + q / r^3 + 5 / (4 * r^2) := by positivity
      calc
        |deriv (fun s : ℝ => heatHessian3 s i j y) r| * ‖y‖^alpha =
            K * (|P| * ‖y‖^alpha) := by
          rw [hderiv, abs_mul, abs_of_nonneg hK]
          ring
        _ ≤ K * (B * ‖y‖^alpha) := by
          apply mul_le_mul_of_nonneg_left _ hK
          exact mul_le_mul_of_nonneg_right (hpoly.trans hred) hnα
        _ ≤ (8 * K₂) * (B * ‖y‖^alpha) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hB hnα)
          simpa [K, K₂] using hkernel
        _ = K₂ * (8 * B * ‖y‖^alpha) := by ring
        _ ≤ K₂ * (64 * (‖y‖^alpha / t^2 + ‖y‖^(alpha+2) / t^3 +
            ‖y‖^(alpha+4) / t^4)) := mul_le_mul_of_nonneg_left hcoeff hK₂
        _ = temporalGaussianEnvelope alpha t y := by
          simp [temporalGaussianEnvelope, K₂]
          ring
    exact hpoint
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
