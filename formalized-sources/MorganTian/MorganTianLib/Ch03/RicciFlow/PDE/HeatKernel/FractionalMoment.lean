import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Basic
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Semigroup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
open Set MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace MorganTianLib.ParabolicPDE
/-- **Math.** Finite fractional moment with the parabolic scaling exponent. -/
theorem gaussianHeatKernel_fractional_moment (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : ℝ => gaussianHeatKernel t x * |x| ^ alpha) volume ∧
      (∫ x : ℝ, gaussianHeatKernel t x * |x| ^ alpha) ≤ C * t ^ (alpha / 2) := by
/- SWARM_PROOF_BEGIN -/
  have hgauss : Integrable
      (fun y : ℝ => |y| ^ alpha * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) volume := by
    have hpos : IntegrableOn
        (fun y : ℝ => y ^ alpha * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) (by linarith)
    have hpos' : IntegrableOn
        (fun y : ℝ => |y| ^ alpha * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) (Ioi 0) := by
      refine hpos.congr_fun (fun y hy => ?_) measurableSet_Ioi
      rw [abs_of_pos (mem_Ioi.mp hy)]
    have hneg : IntegrableOn
        (fun y : ℝ => |y| ^ alpha * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) (Iio 0) := by
      rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding]
      simp only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero]
      refine hpos.congr_fun (fun y hy => ?_) measurableSet_Ioi
      rw [abs_neg, abs_of_pos (mem_Ioi.mp hy)]
    rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
      integrableOn_Ici_iff_integrableOn_Ioi]
    exact ⟨hneg, hpos'⟩
  have h1 : Integrable
      (fun y : ℝ => gaussianHeatKernel 1 y * |y| ^ alpha) volume := by
    have h := hgauss.const_mul ((Real.sqrt (4 * Real.pi))⁻¹)
    convert h using 1
    funext y
    unfold gaussianHeatKernel
    simp only [mul_one]
    have he : -y ^ 2 / 4 = -(1 / 4 : ℝ) * y ^ 2 := by ring
    rw [he]
    ring
  let F : ℝ → ℝ := fun x => gaussianHeatKernel 1 x * |x| ^ alpha
  let M : ℝ := ∫ y : ℝ, F y
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, F]
    apply integral_nonneg_of_ae
    filter_upwards [] with y
    exact mul_nonneg (gaussianHeatKernel_pos (by norm_num) y).le
      (Real.rpow_nonneg (abs_nonneg y) _)
  let C : ℝ := 1 + M
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    linarith
  · intro t ht
    let a : ℝ := Real.sqrt t
    let Ft : ℝ → ℝ := fun x => gaussianHeatKernel t x * |x| ^ alpha
    have ha : 0 < a := by
      dsimp [a]
      exact Real.sqrt_pos.2 ht
    have ha_sq : a ^ 2 = t := by
      dsimp [a]
      exact Real.sq_sqrt ht.le
    have hkernel_scale : ∀ y : ℝ,
        gaussianHeatKernel t (a * y) = a⁻¹ * gaussianHeatKernel 1 y := by
      intro y
      unfold gaussianHeatKernel
      have hsqrt : Real.sqrt (4 * Real.pi * t) =
          Real.sqrt (4 * Real.pi) * a := by
        rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring,
          Real.sqrt_mul (by positivity)]
      rw [hsqrt]
      have hexp : -(a * y) ^ 2 / (4 * t) = -(y ^ 2) / 4 := by
        rw [show (a * y) ^ 2 = a ^ 2 * y ^ 2 by ring, ha_sq]
        field_simp [ht.ne']
      rw [hexp]
      simp only [mul_one]
      ring
    have hscale_rpow : ∀ y : ℝ, |a * y| ^ alpha = a ^ alpha * |y| ^ alpha := by
      intro y
      rw [abs_mul, abs_of_pos ha, Real.mul_rpow ha.le (abs_nonneg y)]
    have hsub : a ^ (alpha - 1) = a⁻¹ * a ^ alpha := by
      rw [Real.rpow_sub ha alpha 1, Real.rpow_one, div_eq_mul_inv]
      ring
    have hcomp_eq : (fun y : ℝ => Ft (a * y)) =
        (fun y : ℝ => a ^ (alpha - 1) * F y) := by
      funext y
      dsimp [Ft, F]
      rw [hkernel_scale y, hscale_rpow y, hsub]
      ring
    have hcomp : Integrable (fun y : ℝ => Ft (a * y)) volume := by
      rw [hcomp_eq]
      exact h1.const_mul _
    have hFt : Integrable Ft volume :=
      (integrable_comp_mul_left_iff Ft ha.ne').mp hcomp
    have hchange : (∫ y : ℝ, Ft (a * y)) = a⁻¹ * ∫ x : ℝ, Ft x := by
      simpa [smul_eq_mul, abs_of_pos (inv_pos.mpr ha)] using
        (Measure.integral_comp_mul_left Ft a)
    have hcomp_int : (∫ y : ℝ, Ft (a * y)) = a ^ (alpha - 1) * M := by
      rw [hcomp_eq, integral_const_mul]
    have hmoment : (∫ x : ℝ, Ft x) = a ^ alpha * M := by
      have heq : a⁻¹ * (∫ x : ℝ, Ft x) = a ^ (alpha - 1) * M :=
        hchange.symm.trans hcomp_int
      calc
        (∫ x : ℝ, Ft x) = a * (a⁻¹ * ∫ x : ℝ, Ft x) := by
          field_simp
        _ = a * (a ^ (alpha - 1) * M) := by rw [heq]
        _ = a ^ alpha * M := by
          rw [Real.rpow_sub ha alpha 1, Real.rpow_one, div_eq_mul_inv]
          field_simp
    have ha_rpow : a ^ alpha = t ^ (alpha / 2) := by
      dsimp [a]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
      congr 1
      ring
    refine ⟨hFt, ?_⟩
    rw [hmoment, ha_rpow]
    dsimp [C]
    have ht_nonneg : 0 ≤ t ^ (alpha / 2) := Real.rpow_nonneg ht.le _
    nlinarith
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
