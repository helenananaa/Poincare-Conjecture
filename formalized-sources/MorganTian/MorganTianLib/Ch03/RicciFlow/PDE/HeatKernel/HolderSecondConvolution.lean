import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Basic
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Semigroup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianCancellation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianEstimate
open Set MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace MorganTianLib.ParabolicPDE
/-- **Math.** Cancellation yields an integrable-in-time Holder gain for the actual Hessian convolution. -/
theorem gaussianHeatKernel_holder_second_convolution (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (H : ℝ), Continuous f → 0 ≤ H →
      (∀ x y, |f x - f y| ≤ H * |x - y| ^ alpha) →
      ∀ t : ℝ, 0 < t → ∀ x : ℝ,
        Integrable (fun y : ℝ => iteratedDeriv 2 (gaussianHeatKernel t) y * f (x - y)) volume ∧
        |∫ y : ℝ, iteratedDeriv 2 (gaussianHeatKernel t) y * f (x - y)| ≤
          C * H * t ^ (alpha / 2 - 1) := by
/- SWARM_PROOF_BEGIN -/
  obtain ⟨C, hC, hbound⟩ :=
    gaussianHeatKernel_hessian_holder_bound alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro f H hf hH hholder t ht x
  obtain ⟨hhess, hmass⟩ := gaussianHeatKernel_hessian_cancellation ht
  obtain ⟨hweight, hweight_bound⟩ := hbound t ht
  let difference : ℝ → ℝ := fun y =>
    iteratedDeriv 2 (gaussianHeatKernel t) y * (f (x - y) - f x)
  have hkernel_cont : Continuous (iteratedDeriv 2 (gaussianHeatKernel t)) := by
    exact (gaussianHeatKernel_derivatives ht).1.continuous_iteratedDeriv 2
      (by
        change ((2 : ℕ∞) : ℕ∞ω) ≤ (∞ : ℕ∞ω)
        exact WithTop.coe_le_coe.2
          (OrderTop.le_top (α := ℕ∞) (2 : ℕ∞)))
  have hshift_cont : Continuous (fun y : ℝ => f (x - y)) := by
    exact hf.comp (continuous_const.sub continuous_id)
  have hdiff_cont : Continuous difference := by
    dsimp [difference]
    exact hkernel_cont.mul (hshift_cont.sub continuous_const)
  have hdiff_dom : Integrable
      (fun y : ℝ => H *
        (|iteratedDeriv 2 (gaussianHeatKernel t) y| * |y| ^ alpha)) volume :=
    hweight.const_mul H
  have hdiff_bound : ∀ y : ℝ,
      ‖difference y‖ ≤ H *
        (|iteratedDeriv 2 (gaussianHeatKernel t) y| * |y| ^ alpha) := by
    intro y
    have hxy : |f (x - y) - f x| ≤ H * |y| ^ alpha := by
      simpa only [show |(x - y) - x| ^ alpha = |y| ^ alpha by
        rw [show (x - y) - x = -y by ring, abs_neg]] using
        hholder (x - y) x
    dsimp [difference]
    rw [abs_mul]
    calc
      |iteratedDeriv 2 (gaussianHeatKernel t) y| *
          |f (x - y) - f x| ≤
          |iteratedDeriv 2 (gaussianHeatKernel t) y| *
            (H * |y| ^ alpha) :=
        mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
      _ = H *
          (|iteratedDeriv 2 (gaussianHeatKernel t) y| * |y| ^ alpha) := by
        ring
  have hdiff_int : Integrable difference volume := by
    apply hdiff_dom.mono' hdiff_cont.aestronglyMeasurable
    filter_upwards [] with y
    exact hdiff_bound y
  have hconst_int : Integrable
      (fun y : ℝ => iteratedDeriv 2 (gaussianHeatKernel t) y * f x) volume :=
    hhess.mul_const _
  have hfull_int : Integrable
      (fun y : ℝ => iteratedDeriv 2 (gaussianHeatKernel t) y * f (x - y)) volume := by
    have hdecomp :
        (fun y : ℝ => iteratedDeriv 2 (gaussianHeatKernel t) y * f (x - y)) =
          (fun y : ℝ => difference y +
            iteratedDeriv 2 (gaussianHeatKernel t) y * f x) := by
      funext y
      dsimp [difference]
      ring
    rw [hdecomp]
    exact hdiff_int.add hconst_int
  have hconst_value :
      (∫ y : ℝ, iteratedDeriv 2 (gaussianHeatKernel t) y * f x) = 0 := by
    rw [integral_mul_const, hmass]
    ring
  have hrewrite :
      (∫ y : ℝ, iteratedDeriv 2 (gaussianHeatKernel t) y * f (x - y)) =
        ∫ y : ℝ, difference y := by
    have hdecomp :
        (fun y : ℝ => iteratedDeriv 2 (gaussianHeatKernel t) y * f (x - y)) =
          (fun y : ℝ => difference y +
            iteratedDeriv 2 (gaussianHeatKernel t) y * f x) := by
      funext y
      dsimp [difference]
      ring
    calc
      (∫ y : ℝ, iteratedDeriv 2 (gaussianHeatKernel t) y * f (x - y)) =
          ∫ y : ℝ, (difference y +
            iteratedDeriv 2 (gaussianHeatKernel t) y * f x) := by rw [hdecomp]
      _ = (∫ y : ℝ, difference y) +
          ∫ y : ℝ, iteratedDeriv 2 (gaussianHeatKernel t) y * f x :=
        integral_add hdiff_int hconst_int
      _ = ∫ y : ℝ, difference y := by rw [hconst_value, add_zero]
  refine ⟨hfull_int, ?_⟩
  calc
    |(∫ y : ℝ, iteratedDeriv 2 (gaussianHeatKernel t) y * f (x - y))| =
        ‖∫ y : ℝ, difference y‖ := by rw [hrewrite]; rfl
    _ ≤ ∫ y : ℝ, H *
        (|iteratedDeriv 2 (gaussianHeatKernel t) y| * |y| ^ alpha) :=
      norm_integral_le_of_norm_le hdiff_dom (Eventually.of_forall hdiff_bound)
    _ = H * (∫ y : ℝ,
        |iteratedDeriv 2 (gaussianHeatKernel t) y| * |y| ^ alpha) := by
      rw [integral_const_mul]
    _ ≤ H * (C * t ^ (alpha / 2 - 1)) :=
      mul_le_mul_of_nonneg_left hweight_bound hH
    _ = C * H * t ^ (alpha / 2 - 1) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
