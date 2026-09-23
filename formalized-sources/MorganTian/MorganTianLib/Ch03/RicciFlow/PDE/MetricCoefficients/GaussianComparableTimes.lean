import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** gaussian comparable times. -/
theorem gaussian_comparable_times 
    (t r : ℝ) (ht : 0 < t) (htr : t ≤ r) (hrt : r ≤ 2*t) (y : E3) :
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 r y ≤
      8*MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2*t) y :=
/- SWARM_PROOF_BEGIN -/
by
  rw [MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_norm_form,
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_norm_form]
  have hrpos : 0 < r := lt_of_lt_of_le ht htr
  have hden : 4 * r ≤ 4 * (2 * t) := by nlinarith
  have hq : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
  have hratio : ‖y‖ ^ 2 / (4 * (2 * t)) ≤ ‖y‖ ^ 2 / (4 * r) := by
    have hd1 : 0 < 4 * r := by positivity
    have hd2 : 0 < 4 * (2 * t) := by positivity
    rw [div_le_div_iff₀ hd2 hd1]
    nlinarith [mul_le_mul_of_nonneg_left hden hq]
  have hexp : -‖y‖ ^ 2 / (4 * r) ≤ -‖y‖ ^ 2 / (4 * (2 * t)) := by
    simpa only [neg_div] using neg_le_neg hratio
  have hExp := Real.exp_le_exp.mpr hexp
  have hnorm :
      (Real.sqrt (4 * Real.pi * r))⁻¹ ^ (3 : ℕ) ≤
        8 * (Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ ^ (3 : ℕ) := by
    let u : ℝ := 4 * Real.pi * r
    let v : ℝ := 4 * Real.pi * (2 * t)
    have hu : 0 < u := by dsimp [u]; positivity
    have hv : 0 < v := by dsimp [v]; positivity
    have hscale : v ≤ 4 * u := by
      dsimp [u, v]
      calc
        4 * Real.pi * (2 * t) ≤ (4 * Real.pi) * (4 * r) :=
          mul_le_mul_of_nonneg_left (by nlinarith [htr]) (by positivity)
        _ = 4 * (4 * Real.pi * r) := by ring
    have hsqrt : Real.sqrt v ≤ 2 * Real.sqrt u := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt (le_of_lt hu)]
    have hhalf : Real.sqrt v / 2 ≤ Real.sqrt u := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have hinv : (Real.sqrt u)⁻¹ ≤ 2 * (Real.sqrt v)⁻¹ := by
      calc
        (Real.sqrt u)⁻¹ ≤ (Real.sqrt v / 2)⁻¹ :=
          by
            simpa only [one_div] using
              (one_div_le_one_div_of_le (by positivity) hhalf)
        _ = 2 * (Real.sqrt v)⁻¹ := by field_simp [ne_of_gt hv]
    change (Real.sqrt u)⁻¹ ^ (3 : ℕ) ≤
      8 * (Real.sqrt v)⁻¹ ^ (3 : ℕ)
    calc
      (Real.sqrt u)⁻¹ ^ (3 : ℕ) ≤ (2 * (Real.sqrt v)⁻¹) ^ (3 : ℕ) := by
        gcongr
      _ = 8 * (Real.sqrt v)⁻¹ ^ (3 : ℕ) := by ring
  calc
    (Real.sqrt (4 * Real.pi * r))⁻¹ ^ (3 : ℕ) *
        Real.exp (-‖y‖ ^ 2 / (4 * r)) ≤
      (8 * (Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ ^ (3 : ℕ)) *
        Real.exp (-‖y‖ ^ 2 / (4 * r)) :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ (8 * (Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ ^ (3 : ℕ)) *
        Real.exp (-‖y‖ ^ 2 / (4 * (2 * t))) :=
      mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = 8 * ((Real.sqrt (4 * Real.pi * (2 * t)))⁻¹ ^ (3 : ℕ) *
        Real.exp (-‖y‖ ^ 2 / (4 * (2 * t)))) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
