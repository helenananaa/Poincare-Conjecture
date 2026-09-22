import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TimeDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatFirstFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatGradientFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatHessianContinuous
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction RealInnerProductSpace
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual first-derivative kernel has a uniformly small terminal-time tail. -/
theorem duhamel_gradient_terminal_tail :
    ∃ C : ℝ, 0<C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (T eps : ℝ), 0≤eps → eps≤T →
      ∀ (x : E3) (i : Fin 3),
        IntervalIntegrable (fun s => ∫ y : E3,
          fderiv ℝ (euclideanHeatKernel 3 (T-s)) y (EuclideanSpace.single i 1)*F (s,x-y)) volume (T-eps) T ∧
        |∫ s in (T-eps)..T, ∫ y : E3,
          fderiv ℝ (euclideanHeatKernel 3 (T-s)) y (EuclideanSpace.single i 1)*F (s,x-y)| ≤
          C*‖F‖*Real.sqrt eps :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨Cg, hCg, hgrad⟩ := euclideanHeatKernel_three_gradient_L1
  let C : ℝ := 2 * Cg
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro F T eps heps hepsT x i
  by_cases heps0 : eps = 0
  · subst eps
    simp
  · let d : ℝ := T - eps
    let q : ℝ → ℝ := fun s => ∫ y : E3,
      fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
        (EuclideanSpace.single i 1)*F (s,x-y)
    let k : ℝ × E3 → ℝ := fun p =>
      if 0 < T - p.1 then
        (-(p.2 i / (2 * (T - p.1))) *
          euclideanHeatKernel 3 (T - p.1) p.2) * F (p.1, x-p.2)
      else 0
    let q₀ : ℝ → ℝ := fun s => ∫ y : E3, k (s,y)
    have hkernel_meas : Measurable k := by
      dsimp [k]
      apply Measurable.ite (by measurability) ?_ measurable_const
      unfold euclideanHeatKernel gaussianHeatKernel
      measurability
    have hq₀_sm : StronglyMeasurable q₀ := by
      simpa [q₀] using hkernel_meas.stronglyMeasurable.integral_prod_right'
    have hqeq (s : ℝ) (hs : s < T) : q s = q₀ s := by
      have hts : 0 < T - s := sub_pos.mpr hs
      dsimp [q, q₀, k]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [if_pos hts, euclideanHeatKernel_three_gradient_formula hts y i]
    have hdt : d ≤ T := by
      dsimp [d]
      linarith
    have hwint : IntervalIntegrable
        (fun s : ℝ => (T-s) ^ (-(1 / 2 : ℝ))) volume d T := by
      have hp : IntervalIntegrable
          (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) volume 0 eps :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      have hcomp := hp.comp_sub_left T
      have hcomp' := hcomp.symm
      simpa [d] using hcomp'
    let w : ℝ → ℝ := fun s => (T-s) ^ (-(1 / 2 : ℝ))
    have hbound : ∀ᵐ s ∂volume, s ∈ Ioc d T →
        ‖q₀ s‖ ≤ Cg * ‖F‖ * w s := by
      filter_upwards [volume.ae_ne T] with s hst hs
      have hslt : s < T := lt_of_le_of_ne hs.2 hst
      have hts : 0 < T - s := sub_pos.mpr hslt
      have hgi := hgrad (T-s) hts i
      have hmajor : Integrable (fun y : E3 => ‖F‖ *
          |fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
            (EuclideanSpace.single i 1)|) volume := by
        simpa [Real.norm_eq_abs, mul_comm] using hgi.1.norm.const_mul ‖F‖
      have hnorm : ‖∫ y : E3, fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
            (EuclideanSpace.single i 1)*F (s,x-y)‖ ≤
          ∫ y : E3, ‖F‖ *
            |fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
              (EuclideanSpace.single i 1)| := by
        apply norm_integral_le_of_norm_le hmajor
        filter_upwards [] with y
        rw [norm_mul, Real.norm_eq_abs]
        calc
          |fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
              (EuclideanSpace.single i 1)| * |F (s,x-y)| ≤
              |fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
                (EuclideanSpace.single i 1)| * ‖F‖ := by
            exact mul_le_mul_of_nonneg_left
              (F.norm_coe_le_norm (s,x-y)) (abs_nonneg _)
          _ = ‖F‖ * |fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
                (EuclideanSpace.single i 1)| := by ring
      rw [← hqeq s hslt]
      calc
        ‖∫ y : E3, fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
            (EuclideanSpace.single i 1)*F (s,x-y)‖ ≤
            ∫ y : E3, ‖F‖ *
              |fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
                (EuclideanSpace.single i 1)| := hnorm
        _ = ‖F‖ * (∫ y : E3, |fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
              (EuclideanSpace.single i 1)|) := by
          rw [integral_const_mul]
        _ ≤ ‖F‖ * (Cg / Real.sqrt (T-s)) :=
          mul_le_mul_of_nonneg_left hgi.2 (norm_nonneg _)
        _ = Cg * ‖F‖ * w s := by
          have hpow : w s = 1 / Real.sqrt (T-s) := by
            dsimp [w]
            rw [Real.rpow_neg (le_of_lt hts), ← Real.sqrt_eq_rpow]
            simp [one_div]
          rw [hpow]
          ring
    have hbound' : (fun s => ‖q₀ s‖) ≤ᵐ[volume.restrict (uIoc d T)]
        (fun s => Cg * ‖F‖ * w s) := by
      rw [uIoc_of_le hdt]
      exact (ae_restrict_iff' measurableSet_Ioc).2 hbound
    have hq₀_int : IntervalIntegrable q₀ volume d T := by
      exact (hwint.const_mul (Cg * ‖F‖)).mono_fun'
        hq₀_sm.aestronglyMeasurable hbound'
    have hqa : q =ᵐ[volume.restrict (uIoc d T)] q₀ := by
      rw [uIoc_of_le hdt]
      apply (ae_restrict_iff' measurableSet_Ioc).2
      filter_upwards [volume.ae_ne T] with s hst hs
      exact hqeq s (lt_of_le_of_ne hs.2 hst)
    have hqint : IntervalIntegrable q volume d T :=
      hq₀_int.congr_ae hqa.symm
    have hw_integral : (∫ s in d..T, w s) = 2 * Real.sqrt eps := by
      calc
        (∫ s in d..T, w s) =
            ∫ r in T-T..T-d, r ^ (-(1 / 2 : ℝ)) := by
          dsimp [w]
          exact intervalIntegral.integral_comp_sub_left
            (f := fun r : ℝ => r ^ (-(1 / 2 : ℝ))) T
        _ = ∫ r in (0 : ℝ)..eps, r ^ (-(1 / 2 : ℝ)) := by
          dsimp [d]
          ring_nf
        _ = 2 * Real.sqrt eps := by
          rw [integral_rpow (a := (0 : ℝ)) (b := eps) (r := -(1 / 2 : ℝ))
            (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
          rw [Real.sqrt_eq_rpow]
          norm_num
          ring
    refine ⟨?_, ?_⟩
    · change IntervalIntegrable q volume d T
      exact hqint
    · have hnorm := intervalIntegral.norm_integral_le_of_norm_le hdt hbound
        (hwint.const_mul (Cg * ‖F‖))
      rw [show |∫ s in d..T, q s| = ‖∫ s in d..T, q s‖ by rfl]
      rw [intervalIntegral.integral_congr_ae_restrict hqa]
      calc
        ‖∫ s in d..T, q₀ s‖ ≤
            ∫ s in d..T, Cg * ‖F‖ * w s := hnorm
        _ = (Cg * ‖F‖) * (∫ s in d..T, w s) := by
          simpa only [mul_assoc] using
            (intervalIntegral.integral_const_mul (μ := volume)
              (a := d) (b := T) (Cg * ‖F‖) w)
        _ = C * ‖F‖ * Real.sqrt eps := by
          rw [hw_integral]
          dsimp [C]
          ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
