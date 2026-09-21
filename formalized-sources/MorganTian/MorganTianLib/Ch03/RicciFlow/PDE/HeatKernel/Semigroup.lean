import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace MorganTianLib.ParabolicPDE
/-- **Math.** Actual Gaussian normalization and convolution-semigroup identity. -/
theorem gaussianHeatKernel_mass_semigroup :
    (∀ t : ℝ, 0 < t → Integrable (gaussianHeatKernel t) volume ∧
      (∫ x : ℝ, gaussianHeatKernel t x) = 1) ∧
    ∀ t s : ℝ, 0 < t → 0 < s → ∀ x : ℝ,
      Integrable (fun y : ℝ => gaussianHeatKernel t (x - y) * gaussianHeatKernel s y) volume ∧
      (∫ y : ℝ, gaussianHeatKernel t (x - y) * gaussianHeatKernel s y) =
        gaussianHeatKernel (t + s) x := by
/- SWARM_PROOF_BEGIN -/
  constructor
  · intro t ht
    have hcoef : 0 < (1 / (4 * t) : ℝ) := by positivity
    have hgauss : Integrable (fun z : ℝ => Real.exp (-(1 / (4 * t)) * z ^ 2)) volume :=
      integrable_exp_neg_mul_sq hcoef
    have hkernel : gaussianHeatKernel t =
        fun z : ℝ => (Real.sqrt (4 * Real.pi * t))⁻¹ *
          Real.exp (-(1 / (4 * t)) * z ^ 2) := by
      funext z
      unfold gaussianHeatKernel
      congr 1
      ring
    constructor
    · rw [hkernel]
      exact hgauss.const_mul _
    · rw [hkernel, integral_const_mul, integral_gaussian]
      have harg : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by
        field_simp [ht.ne']
      rw [harg]
      exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  · intro t s ht hs x
    have hts : 0 < t + s := by linarith
    let a : ℝ := (t + s) / (4 * t * s)
    let m : ℝ := s * x / (t + s)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hquad : ∀ y : ℝ,
        -(x - y) ^ 2 / (4 * t) + -(y ^ 2) / (4 * s) =
          -(x ^ 2) / (4 * (t + s)) - a * (y - m) ^ 2 := by
      intro y
      dsimp [a, m]
      field_simp [ht.ne', hs.ne', hts.ne']
      ring
    have hprod :
        (fun y : ℝ => gaussianHeatKernel t (x - y) * gaussianHeatKernel s y) =
          (fun y : ℝ =>
            ((Real.sqrt (4 * Real.pi * t))⁻¹ *
                (Real.sqrt (4 * Real.pi * s))⁻¹ *
                Real.exp (-(x ^ 2) / (4 * (t + s)))) *
              Real.exp (-a * (y - m) ^ 2)) := by
      funext y
      unfold gaussianHeatKernel
      calc
        ((Real.sqrt (4 * Real.pi * t))⁻¹ *
              Real.exp (-(x - y) ^ 2 / (4 * t))) *
            ((Real.sqrt (4 * Real.pi * s))⁻¹ *
              Real.exp (-(y ^ 2) / (4 * s))) =
            (Real.sqrt (4 * Real.pi * t))⁻¹ *
              (Real.sqrt (4 * Real.pi * s))⁻¹ *
              (Real.exp (-(x - y) ^ 2 / (4 * t)) *
                Real.exp (-(y ^ 2) / (4 * s))) := by ring
        _ = (Real.sqrt (4 * Real.pi * t))⁻¹ *
              (Real.sqrt (4 * Real.pi * s))⁻¹ *
              Real.exp (-(x - y) ^ 2 / (4 * t) +
                -(y ^ 2) / (4 * s)) := by
              rw [← Real.exp_add]
        _ = ((Real.sqrt (4 * Real.pi * t))⁻¹ *
              (Real.sqrt (4 * Real.pi * s))⁻¹ *
            Real.exp (-(x ^ 2) / (4 * (t + s)))) *
            Real.exp (-a * (y - m) ^ 2) := by
              have he : -(x ^ 2) / (4 * (t + s)) - a * (y - m) ^ 2 =
                  -(x ^ 2) / (4 * (t + s)) + -(a * (y - m) ^ 2) := by ring
              rw [hquad y, he, Real.exp_add]
              ring
    have hshift : Integrable (fun y : ℝ => Real.exp (-a * (y - m) ^ 2)) volume := by
      simpa [sub_eq_add_neg] using
        (integrable_exp_neg_mul_sq ha).comp_add_right (-m)
    have hprod_int : Integrable
        (fun y : ℝ =>
          ((Real.sqrt (4 * Real.pi * t))⁻¹ *
              (Real.sqrt (4 * Real.pi * s))⁻¹ *
              Real.exp (-(x ^ 2) / (4 * (t + s)))) *
            Real.exp (-a * (y - m) ^ 2)) volume :=
      hshift.const_mul _
    constructor
    · rw [hprod]
      exact hprod_int
    · have htranslation :
          (∫ y : ℝ, Real.exp (-a * (y - m) ^ 2)) = Real.sqrt (Real.pi / a) := by
        calc
          (∫ y : ℝ, Real.exp (-a * (y - m) ^ 2)) =
              ∫ y : ℝ, Real.exp (-a * y ^ 2) := by
                calc
                  (∫ y : ℝ, Real.exp (-a * (y - m) ^ 2)) =
                      ∫ y : ℝ, Real.exp (-a * (y + (-m)) ^ 2) := by
                    apply integral_congr_ae
                    filter_upwards [] with y
                    congr 2
                  _ = ∫ y : ℝ, Real.exp (-a * y ^ 2) :=
                    integral_add_right_eq_self
                      (fun y : ℝ => Real.exp (-a * y ^ 2)) (-m)
          _ = Real.sqrt (Real.pi / a) := integral_gaussian a
      have hnorm :
          (Real.sqrt (4 * Real.pi * t))⁻¹ *
              (Real.sqrt (4 * Real.pi * s))⁻¹ *
              Real.sqrt (Real.pi / a) =
            (Real.sqrt (4 * Real.pi * (t + s)))⁻¹ := by
        apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
        have hpt : 0 ≤ 4 * Real.pi * t := by positivity
        have hps : 0 ≤ 4 * Real.pi * s := by positivity
        have hpts : 0 ≤ 4 * Real.pi * (t + s) := by positivity
        have hpa : 0 ≤ Real.pi / a := by positivity
        simp only [mul_pow, inv_pow]
        rw [Real.sq_sqrt hpt, Real.sq_sqrt hps, Real.sq_sqrt hpts,
          Real.sq_sqrt hpa]
        dsimp [a]
        field_simp [ht.ne', hs.ne', hts.ne']
      rw [hprod, integral_const_mul, htranslation]
      unfold gaussianHeatKernel
      calc
        (Real.sqrt (4 * Real.pi * t))⁻¹ *
              (Real.sqrt (4 * Real.pi * s))⁻¹ *
              Real.exp (-(x ^ 2) / (4 * (t + s))) *
              Real.sqrt (Real.pi / a) =
            ((Real.sqrt (4 * Real.pi * t))⁻¹ *
              (Real.sqrt (4 * Real.pi * s))⁻¹ *
              Real.sqrt (Real.pi / a)) *
              Real.exp (-(x ^ 2) / (4 * (t + s))) := by ring
        _ = (Real.sqrt (4 * Real.pi * (t + s)))⁻¹ *
              Real.exp (-(x ^ 2) / (4 * (t + s))) := by rw [hnorm]
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
