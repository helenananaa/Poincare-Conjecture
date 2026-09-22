import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatTimeDerivativeL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatTimeEquation
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The off-center quadratic Gaussian tail is negligible after division by time. -/
theorem heat_kernel_quadratic_tail_small_time (r : ℝ) (hr : 0<r) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ y : E3 in {z | r≤‖z‖},
      euclideanHeatKernel 3 t y*(1+‖y‖^2)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, hmoment⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (4 : ℝ) (by norm_num)
  let S : Set E3 := {y | r ≤ ‖y‖}
  let A : ℝ := (r⁻¹) ^ 4 + (r⁻¹) ^ 2
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have htail_le : ∀ t : ℝ, 0 < t →
      (∫ y : E3 in S, euclideanHeatKernel 3 t y * (1 + ‖y‖ ^ (2 : ℕ))) ≤
        A * (C * t ^ (2 : ℕ)) := by
    intro t ht
    let K : E3 → ℝ := fun y => euclideanHeatKernel 3 t y
    let G : E3 → ℝ := fun y => K y * ‖y‖ ^ (4 : ℕ)
    let H : E3 → ℝ := fun y => A * G y
    have hKcont : Continuous K := by
      dsimp [K]
      unfold euclideanHeatKernel
      exact (contDiff_prod (fun i _ =>
        (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
    have hG : Integrable G volume := by
      dsimp [G, K]
      simpa [Real.rpow_natCast] using (hmoment t ht).1
    have hH : Integrable H volume := by
      dsimp [H]
      exact hG.const_mul A
    have hH_nonneg : ∀ y, 0 ≤ H y := by
      intro y
      dsimp [H, G]
      exact mul_nonneg hA
        (mul_nonneg (euclideanHeatKernel_pos 3 ht y).le (by positivity))
    have hpoint (y : E3) (hy : y ∈ S) :
        K y * (1 + ‖y‖ ^ (2 : ℕ)) ≤ H y := by
      have hyr : r ≤ ‖y‖ := by simpa [S] using hy
      have hr0 : 0 ≤ r := hr.le
      have hnorm : 0 ≤ ‖y‖ := norm_nonneg y
      have hsq : r ^ 2 ≤ ‖y‖ ^ 2 := by
        nlinarith [mul_self_le_mul_self hr0 hyr]
      have hfour : r ^ 4 ≤ ‖y‖ ^ 4 := by
        nlinarith [mul_self_le_mul_self (sq_nonneg r) hsq]
      have hrad : 1 + ‖y‖ ^ (2 : ℕ) ≤
          ((r⁻¹) ^ 4 + (r⁻¹) ^ 2) * ‖y‖ ^ (4 : ℕ) := by
        have h₁ : 1 ≤ r⁻¹ ^ 4 * ‖y‖ ^ 4 := by
          have hh := mul_le_mul_of_nonneg_left hfour
            (by positivity : 0 ≤ r⁻¹ ^ 4)
          calc
            1 = r⁻¹ ^ 4 * r ^ 4 := by field_simp [hr.ne']
            _ ≤ r⁻¹ ^ 4 * ‖y‖ ^ 4 := hh
        have h₂ : ‖y‖ ^ 2 ≤ r⁻¹ ^ 2 * ‖y‖ ^ 4 := by
          have hsqmul : r ^ 2 * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 * ‖y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
          have hh := mul_le_mul_of_nonneg_left hsqmul
            (by positivity : 0 ≤ r⁻¹ ^ 2)
          calc
            ‖y‖ ^ 2 = r⁻¹ ^ 2 * (r ^ 2 * ‖y‖ ^ 2) := by
              field_simp [hr.ne']
            _ ≤ r⁻¹ ^ 2 * (‖y‖ ^ 2 * ‖y‖ ^ 2) := hh
            _ = r⁻¹ ^ 2 * ‖y‖ ^ 4 := by ring
        nlinarith
      calc
        K y * (1 + ‖y‖ ^ (2 : ℕ)) ≤
            K y * (((r⁻¹) ^ 4 + (r⁻¹) ^ 2) * ‖y‖ ^ (4 : ℕ)) :=
          mul_le_mul_of_nonneg_left hrad
            (euclideanHeatKernel_pos 3 ht y).le
        _ = H y := by
          dsimp [H, G]
          ring
    have hFcont : Continuous (fun y : E3 => K y * (1 + ‖y‖ ^ (2 : ℕ))) := by
      exact hKcont.mul (continuous_const.add (continuous_norm.pow 2))
    have hH_on : IntegrableOn H S volume := hH.integrableOn
    have hF_on : IntegrableOn
        (fun y : E3 => K y * (1 + ‖y‖ ^ (2 : ℕ))) S volume := by
      apply Integrable.mono' hH_on
        hFcont.measurable.aestronglyMeasurable.restrict
      filter_upwards [ae_restrict_mem hS] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hpoint y hy
      · dsimp [K]
        exact mul_nonneg (euclideanHeatKernel_pos 3 ht y).le (by positivity)
    calc
      (∫ y : E3 in S, K y * (1 + ‖y‖ ^ (2 : ℕ))) ≤ ∫ y : E3 in S, H y :=
        setIntegral_mono_on hF_on hH_on hS hpoint
      _ ≤ ∫ y : E3, H y :=
        setIntegral_le_integral hH (Eventually.of_forall hH_nonneg)
      _ = A * (∫ y : E3, G y) := by
        dsimp [H]
        rw [integral_const_mul]
      _ ≤ A * (C * t ^ (2 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        have hm := (hmoment t ht).2
        have htpow : t ^ (4 / 2 : ℝ) = t ^ (2 : ℕ) := by
          norm_num [Real.rpow_natCast]
        rw [htpow] at hm
        simpa [G, K, Real.rpow_natCast] using hm
  have hzero : Tendsto (fun t : ℝ => A * C * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    simpa only [mul_zero] using
      ((tendsto_const_nhds.mul hid) :
        Tendsto (fun t : ℝ => (A * C) * t) (𝓝[>] (0 : ℝ))
          (𝓝 ((A * C) * 0)))
  refine squeeze_zero' ?_ ?_ hzero
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hnonneg : 0 ≤ ∫ y : E3 in S,
        euclideanHeatKernel 3 t y * (1 + ‖y‖ ^ (2 : ℕ)) := by
      apply integral_nonneg_of_ae
      filter_upwards [] with y
      exact mul_nonneg (euclideanHeatKernel_pos 3 ht y).le (by positivity)
    exact mul_nonneg (inv_nonneg.mpr ht.le) hnonneg
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hbound := htail_le t ht
    calc
      t⁻¹ * (∫ y : E3 in S,
          euclideanHeatKernel 3 t y * (1 + ‖y‖ ^ (2 : ℕ))) ≤
          t⁻¹ * (A * (C * t ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr ht.le)
      _ = A * C * t := by
        have ht0 : 0 < t := ht
        field_simp [ht0.ne']
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
