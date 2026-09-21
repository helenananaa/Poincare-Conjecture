import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Basic
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Semigroup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FractionalMoment
open Set MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace MorganTianLib.ParabolicPDE
/-- **Math.** Actual convolution recovers Holder initial data with a uniform spatial rate. -/
theorem gaussianHeatKernel_holder_initial_trace (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (H : ℝ), Continuous f → 0 ≤ H →
      (∀ x y, |f x - f y| ≤ H * |x - y| ^ alpha) →
      ∀ t : ℝ, 0 < t → ∀ x : ℝ,
        Integrable (fun y : ℝ => gaussianHeatKernel t y * f (x - y)) volume ∧
        |(∫ y : ℝ, gaussianHeatKernel t y * f (x - y)) - f x| ≤
          C * H * t ^ (alpha / 2) := by
/- SWARM_PROOF_BEGIN -/
  obtain ⟨C, hC, hmoment⟩ := gaussianHeatKernel_fractional_moment alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro f H hf hH hholder t ht x
  obtain ⟨hkernel, hmass⟩ := (gaussianHeatKernel_mass_semigroup.1 t ht)
  obtain ⟨hmoment_int, hmoment_bound⟩ := hmoment t ht
  have hkernel_cont : Continuous (gaussianHeatKernel t) := by
    unfold gaussianHeatKernel
    fun_prop
  have hbase_cont : Continuous
      (fun y : ℝ => gaussianHeatKernel t y * f (x - y)) := by
    fun_prop
  have hconst_int : Integrable
      (fun y : ℝ => gaussianHeatKernel t y * |f x|) volume :=
    hkernel.mul_const _
  have hweighted_int : Integrable
      (fun y : ℝ => H * (gaussianHeatKernel t y * |y| ^ alpha)) volume :=
    hmoment_int.const_mul H
  have hdom_int : Integrable
      (fun y : ℝ => gaussianHeatKernel t y *
        (|f x| + H * |y| ^ alpha)) volume := by
    have heq :
        (fun y : ℝ => gaussianHeatKernel t y *
          (|f x| + H * |y| ^ alpha)) =
        (fun y : ℝ => gaussianHeatKernel t y * |f x|) +
            (fun y : ℝ => H * (gaussianHeatKernel t y * |y| ^ alpha)) := by
      funext y
      change gaussianHeatKernel t y * (|f x| + H * |y| ^ alpha) =
        gaussianHeatKernel t y * |f x| +
          H * (gaussianHeatKernel t y * |y| ^ alpha)
      ring
    rw [heq]
    exact hconst_int.add hweighted_int
  have hbase_bound : ∀ y : ℝ,
      |gaussianHeatKernel t y * f (x - y)| ≤
        gaussianHeatKernel t y * (|f x| + H * |y| ^ alpha) := by
    intro y
    have hy : |(x - y) - x| ^ alpha = |y| ^ alpha := by
      rw [show (x - y) - x = -y by ring, abs_neg]
    rw [abs_mul, abs_of_pos (gaussianHeatKernel_pos ht y)]
    apply mul_le_mul_of_nonneg_left _ (gaussianHeatKernel_pos ht y).le
    calc
      |f (x - y)| ≤ |f x| + |f (x - y) - f x| := by
        calc
          |f (x - y)| = |f x + (f (x - y) - f x)| := by congr 1 <;> ring
          _ ≤ |f x| + |f (x - y) - f x| := abs_add_le _ _
      _ ≤ |f x| + H * |y| ^ alpha := by
        have hxy : |f (x - y) - f x| ≤ H * |y| ^ alpha := by
          simpa [hy] using hholder (x - y) x
        exact add_le_add_right hxy _
  have hbase_int : Integrable
      (fun y : ℝ => gaussianHeatKernel t y * f (x - y)) volume := by
    apply hdom_int.mono' hbase_cont.aestronglyMeasurable
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs] using hbase_bound y
  have hconst_value :
      (∫ y : ℝ, gaussianHeatKernel t y * f x) = f x := by
    rw [integral_mul_const, hmass]
    ring
  let difference : ℝ → ℝ := fun y =>
    gaussianHeatKernel t y * (f (x - y) - f x)
  have hdiff_cont : Continuous difference := by
    dsimp [difference]
    fun_prop
  have hdiff_dom : Integrable
      (fun y : ℝ => H * (gaussianHeatKernel t y * |y| ^ alpha)) volume :=
    hmoment_int.const_mul H
  have hdiff_bound : ∀ y : ℝ,
      ‖difference y‖ ≤ H * (gaussianHeatKernel t y * |y| ^ alpha) := by
    intro y
    dsimp [difference]
    rw [abs_mul, abs_of_pos (gaussianHeatKernel_pos ht y)]
    calc
      gaussianHeatKernel t y * |f (x - y) - f x| ≤
          gaussianHeatKernel t y * (H * |y| ^ alpha) := by
        apply mul_le_mul_of_nonneg_left _ (gaussianHeatKernel_pos ht y).le
        simpa [show |(x - y) - x| ^ alpha = |y| ^ alpha by
          rw [show (x - y) - x = -y by ring, abs_neg]] using
          hholder (x - y) x
      _ = H * (gaussianHeatKernel t y * |y| ^ alpha) := by ring
  have hdiff_int : Integrable difference volume := by
    apply hdiff_dom.mono' hdiff_cont.aestronglyMeasurable
    filter_upwards [] with y
    exact hdiff_bound y
  have hrewrite :
      (∫ y : ℝ, gaussianHeatKernel t y * f (x - y)) - f x =
        ∫ y : ℝ, difference y := by
    calc
      (∫ y : ℝ, gaussianHeatKernel t y * f (x - y)) - f x =
          (∫ y : ℝ, gaussianHeatKernel t y * f (x - y)) -
            (∫ y : ℝ, gaussianHeatKernel t y * f x) := by rw [hconst_value]
      _ = ∫ y : ℝ, (gaussianHeatKernel t y * f (x - y) -
          gaussianHeatKernel t y * f x) :=
        (integral_sub hbase_int (hkernel.mul_const _)).symm
      _ = ∫ y : ℝ, difference y := by
        apply integral_congr_ae
        filter_upwards [] with y
        dsimp [difference]
        ring
  refine ⟨hbase_int, ?_⟩
  calc
      |(∫ y : ℝ, gaussianHeatKernel t y * f (x - y)) - f x| =
          ‖∫ y : ℝ, difference y‖ := by rw [hrewrite]; rfl
      _ ≤ ∫ y : ℝ, H * (gaussianHeatKernel t y * |y| ^ alpha) :=
        norm_integral_le_of_norm_le hdiff_dom (Eventually.of_forall hdiff_bound)
      _ = H * (∫ y : ℝ, gaussianHeatKernel t y * |y| ^ alpha) := by
        rw [integral_const_mul]
      _ ≤ H * (C * t ^ (alpha / 2)) :=
        mul_le_mul_of_nonneg_left hmoment_bound hH
      _ = C * H * t ^ (alpha / 2) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
