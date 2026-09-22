import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveJointSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideHessianUnweighted
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual Duhamel integral of bounded forcing has the small-time sup bound. -/
theorem euclideanHeatKernel_three_bounded_duhamel (F : (ℝ × E3) →ᵇ ℝ)
    (T : ℝ) (hT : 0 ≤ T) (x : E3) :
    IntervalIntegrable (fun s => ∫ y : E3, euclideanHeatKernel 3 (T-s) y * F (s,x-y)) volume 0 T ∧
    |∫ s in (0:ℝ)..T, ∫ y : E3, euclideanHeatKernel 3 (T-s) y * F (s,x-y)| ≤ T*‖F‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  by_cases hT0 : T = 0
  · subst T
    simp
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
    let g : ℝ → ℝ := fun s =>
      ∫ y : E3, euclideanHeatKernel 3 (T - s) y * F (s, x - y)
    have hkernel_meas : Measurable (fun p : ℝ × E3 =>
        euclideanHeatKernel 3 (T - p.1) p.2 * F (p.1, x - p.2)) := by
      unfold euclideanHeatKernel gaussianHeatKernel
      measurability
    have hg_sm : StronglyMeasurable g := by
      simpa [g] using hkernel_meas.stronglyMeasurable.integral_prod_right'
    have hbound : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) T →
        ‖g s‖ ≤ ‖F‖ := by
      filter_upwards [volume.ae_ne T] with s hst hs
      have hslt : s < T := lt_of_le_of_ne hs.2 hst
      have hts : 0 < T - s := sub_pos.mpr hslt
      have hpos := (euclideanHeatKernel_mass_semigroup 3).1 (T - s) hts
      have hmeas : AEStronglyMeasurable (fun y : E3 => F (s, x - y)) volume := by
        fun_prop
      have hint : Integrable
          (fun y : E3 => euclideanHeatKernel 3 (T - s) y * F (s, x - y)) volume := by
        apply hpos.1.mul_bdd hmeas
        exact Eventually.of_forall (fun y => F.norm_coe_le_norm (s, x - y))
      have hnorm : ‖g s‖ ≤ ∫ y : E3, euclideanHeatKernel 3 (T - s) y * ‖F‖ := by
        change ‖∫ y : E3,
          euclideanHeatKernel 3 (T - s) y * F (s, x - y)‖ ≤ _
        refine norm_integral_le_of_norm_le (hpos.1.mul_const ‖F‖) ?_
        filter_upwards [] with y
        have hky : 0 ≤ euclideanHeatKernel 3 (T - s) y :=
          (euclideanHeatKernel_pos 3 hts y).le
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hky]
        gcongr
        exact F.norm_coe_le_norm (s, x - y)
      rw [integral_mul_const, hpos.2, one_mul] at hnorm
      exact hnorm
    have hconstint : IntervalIntegrable (fun _ : ℝ => ‖F‖) volume 0 T :=
      intervalIntegrable_const
    have hbound' : (fun s => ‖g s‖) ≤ᵐ[volume.restrict (uIoc (0 : ℝ) T)]
        (fun _ => ‖F‖) := by
      rw [uIoc_of_le hT]
      exact (ae_restrict_iff' measurableSet_Ioc).2 hbound
    have hg_int : IntervalIntegrable g volume 0 T :=
      hconstint.mono_fun' hg_sm.aestronglyMeasurable hbound'
    refine ⟨?_, ?_⟩
    · simpa [g] using hg_int
    · have hnorm := intervalIntegral.norm_integral_le_of_norm_le hT hbound hconstint
      rw [show |∫ s in (0 : ℝ)..T, g s| = ‖∫ s in (0 : ℝ)..T, g s‖ by rfl]
      simpa [g] using hnorm
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
