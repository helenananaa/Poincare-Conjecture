import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanBasic
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Semigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Equation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderTimeKernel
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderSecondConvolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators
noncomputable section
namespace MorganTianLib.ParabolicPDE
/-- **Math.** Time integrability and a small-time bound for the actual heat-Hessian convolution. -/
theorem gaussianHeatKernel_duhamel_holder_control (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ × ℝ → ℝ), Continuous F →
      ∀ (H T : ℝ), 0 ≤ H → 0 ≤ T →
      (∀ s ∈ Icc (0 : ℝ) T, ∀ x y : ℝ,
        |F (s, x) - F (s, y)| ≤ H * |x - y| ^ alpha) →
      ∀ x : ℝ,
        IntervalIntegrable
          (fun s => ∫ y : ℝ, iteratedDeriv 2 (gaussianHeatKernel (T - s)) y * F (s, x - y))
          volume 0 T ∧
        |∫ s in (0 : ℝ)..T, ∫ y : ℝ,
          iteratedDeriv 2 (gaussianHeatKernel (T - s)) y * F (s, x - y)| ≤
          C * H * T ^ (alpha / 2) := by
/- SWARM_PROOF_BEGIN -/
  obtain ⟨C₀, hC₀, hspatial⟩ :=
    gaussianHeatKernel_holder_second_convolution alpha ha ha1
  let C : ℝ := (2 / alpha) * C₀
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro F hF H T hH hT hholder x
  by_cases hT0 : T = 0
  · subst T
    simp
    positivity
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
    let g : ℝ → ℝ := fun s =>
      ∫ y : ℝ, iteratedDeriv 2 (gaussianHeatKernel (T - s)) y * F (s, x - y)
    let g₀ : ℝ → ℝ := fun s =>
      ∫ y : ℝ, gaussianHeatHessian (T - s) y * F (s, x - y)
    let w : ℝ → ℝ := fun s => C₀ * H * (T - s) ^ (alpha / 2 - 1)
    have hconvolution_eq : ∀ s ∈ Ioc (0 : ℝ) T, s ≠ T →
        g s = g₀ s := by
      intro s hs hst
      have hts : 0 < T - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
      have hderiv : ∀ y : ℝ,
          iteratedDeriv 2 (gaussianHeatKernel (T - s)) y =
            gaussianHeatHessian (T - s) y := by
        intro y
        exact ((gaussianHeatKernel_derivatives hts).2 y).2.1
      dsimp [g, g₀]
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        change iteratedDeriv 2 (gaussianHeatKernel (T - s)) y * F (s, x - y) =
          gaussianHeatHessian (T - s) y * F (s, x - y)
        rw [hderiv y])
    have hkernel_meas : Measurable (fun p : ℝ × ℝ =>
        gaussianHeatHessian (T - p.1) p.2 * F (p.1, x - p.2)) := by
      unfold gaussianHeatHessian gaussianHeatKernel
      measurability
    have hg₀_sm : StronglyMeasurable g₀ := by
      have hsm := hkernel_meas.stronglyMeasurable
      simpa [g₀, ProbabilityTheory.Kernel.const_apply] using
        (hsm.integral_kernel_prod_right'
          (κ := ProbabilityTheory.Kernel.const ℝ volume))
    have hga : g =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] g₀ := by
      apply (ae_restrict_iff' measurableSet_Ioc).2
      filter_upwards [volume.ae_ne T] with s hst hs
      exact hconvolution_eq s hs hst
    obtain ⟨hwt, hweq⟩ :=
      holderTimeKernel_integrable_integral (alpha := alpha) (T := T) ha
    have hwint : IntervalIntegrable w volume 0 T := by
      simpa [w] using hwt.const_mul (C₀ * H)
    have hgbound : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) T →
        ‖g₀ s‖ ≤ w s := by
      filter_upwards [volume.ae_ne T] with s hst hs
      have hslt : s < T := lt_of_le_of_ne hs.2 hst
      have hFs : Continuous (fun y : ℝ => F (s, y)) := by
        exact hF.comp (continuous_const.prodMk continuous_id)
      have hholder_s : ∀ u v : ℝ,
          |F (s, u) - F (s, v)| ≤ H * |u - v| ^ alpha :=
        hholder s ⟨le_of_lt hs.1, hs.2⟩
      obtain ⟨_, hb⟩ := hspatial (fun y : ℝ => F (s, y)) H hFs hH
        hholder_s (T - s) (sub_pos.mpr hslt) x
      change ‖g₀ s‖ ≤ w s
      rw [Real.norm_eq_abs, ← hconvolution_eq s hs hst]
      simpa [g] using hb
    have hgbound' : (fun s => ‖g₀ s‖) ≤ᵐ[volume.restrict (uIoc 0 T)] w := by
      rw [uIoc_of_le hT]
      exact (ae_restrict_iff' measurableSet_Ioc).2 hgbound
    have hg₀int : IntervalIntegrable g₀ volume 0 T := by
      exact hwint.mono_fun' hg₀_sm.aestronglyMeasurable
        hgbound'
    have hga' : g =ᵐ[volume.restrict (uIoc (0 : ℝ) T)] g₀ := by
      rw [uIoc_of_le hT]
      exact hga
    have gint : IntervalIntegrable g volume 0 T :=
      hg₀int.congr_ae hga'.symm
    refine ⟨?_, ?_⟩
    · simpa [g] using gint
    · have hnorm := intervalIntegral.norm_integral_le_of_norm_le hT
        hgbound hwint
      have hconst : (∫ s in (0 : ℝ)..T, w s) =
          C₀ * H * ((2 / alpha) * T ^ (alpha / 2)) := by
        dsimp [w]
        rw [intervalIntegral.integral_const_mul, hweq]
      rw [show |∫ s in (0 : ℝ)..T, g s| =
          ‖∫ s in (0 : ℝ)..T, g s‖ by rfl]
      rw [intervalIntegral.integral_congr_ae_restrict hga']
      rw [hconst] at hnorm
      calc
        ‖∫ s in (0 : ℝ)..T, g₀ s‖ ≤
            C₀ * H * ((2 / alpha) * T ^ (alpha / 2)) := hnorm
        _ = C * H * T ^ (alpha / 2) := by
          dsimp [C]
          ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
