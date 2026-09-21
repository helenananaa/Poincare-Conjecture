import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Equation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace MorganTianLib.ParabolicPDE
/-- **Math.** A genuine weighted L1 bound for the second spatial derivative,
with time exponent integrable near zero for positive Holder exponent. -/
theorem gaussianHeatKernel_hessian_holder_bound (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : ℝ => |iteratedDeriv 2 (gaussianHeatKernel t) x| * |x| ^ alpha) volume ∧
      (∫ x : ℝ, |iteratedDeriv 2 (gaussianHeatKernel t) x| * |x| ^ alpha) ≤
        C * t ^ (alpha / 2 - 1) := by
/- SWARM_PROOF_BEGIN -/
  have habs_exp : ∀ s : ℝ, -1 < s →
      Integrable (fun y : ℝ => |y| ^ s * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) volume := by
    intro s hs
    have hpos : IntegrableOn
        (fun y : ℝ => |y| ^ s * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) (Ioi (0 : ℝ)) := by
      refine (integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 4 : ℝ)) (by norm_num) hs).congr_fun ?_
        measurableSet_Ioi
      intro y hy
      have hy' : 0 < y := hy
      simp [abs_of_pos hy']
    have hneg : IntegrableOn
        (fun y : ℝ => |y| ^ s * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) (Iio (0 : ℝ)) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding (fun y : ℝ => -y) :=
        (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero]
      simpa only [neg_sq] using hpos
    rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union]
    refine ⟨hneg, ?_⟩
    exact (integrableOn_Ici_iff_integrableOn_Ioi).2 hpos

  have hmajor : Integrable
      (fun y : ℝ => (1 + |y| ^ 2) * |y| ^ alpha *
        Real.exp (-(1 / 4 : ℝ) * y ^ 2)) volume := by
    have hα := habs_exp alpha (by linarith)
    have hα2 := habs_exp (alpha + 2) (by linarith)
    have heq : (fun y : ℝ => (1 + |y| ^ 2) * |y| ^ alpha *
        Real.exp (-(1 / 4 : ℝ) * y ^ 2)) =
        (fun y : ℝ => |y| ^ alpha * Real.exp (-(1 / 4 : ℝ) * y ^ 2) +
          |y| ^ (alpha + 2) * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) := by
      funext y
      rw [Real.rpow_add' (abs_nonneg y) (by linarith), Real.rpow_two]
      ring
    rw [heq]
    apply Integrable.congr (hα.add hα2)
    filter_upwards [] with y
    rfl

  have hkernel1 : Integrable
      (fun y : ℝ => |iteratedDeriv 2 (gaussianHeatKernel 1) y| * |y| ^ alpha) volume := by
    have hderiv1 := gaussianHeatKernel_derivatives (t := (1 : ℝ)) (by norm_num)
    have hm := hmajor.const_mul ((Real.sqrt (4 * Real.pi))⁻¹)
    apply Integrable.mono' hm
    · have hcont : Continuous (iteratedDeriv 2 (gaussianHeatKernel 1)) :=
        hderiv1.1.continuous_iteratedDeriv 2
          (by
            change ((2 : ℕ∞) : ℕ∞ω) ≤ (∞ : ℕ∞ω)
            exact WithTop.coe_le_coe.2
              (OrderTop.le_top (α := ℕ∞) (2 : ℕ∞)))
      have hpow : Continuous (fun y : ℝ => |y| ^ alpha) :=
        continuous_abs.rpow_const (fun _ => Or.inr ha.le)
      exact ((hcont.abs.mul hpow).aestronglyMeasurable)
    · filter_upwards [] with y
      have hess : iteratedDeriv 2 (gaussianHeatKernel 1) y =
          gaussianHeatHessian 1 y := (hderiv1.2 y).2.1
      rw [hess]
      unfold gaussianHeatHessian gaussianHeatKernel
      have hcoef : |y ^ 2 / 4 - 1 / 2| ≤ 1 + |y| ^ 2 := by
        rw [abs_le]
        have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
        constructor <;> nlinarith [sq_nonneg y]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abs_nonneg _),
        abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _)]
      norm_num
      ring_nf
      have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
      simp only [abs_of_pos hpi]
      have hcoef' : |-1 / 2 + y ^ 2 * (1 / 4 : ℝ)| ≤ 1 + y ^ 2 := by
        convert hcoef using 1
        · congr 1
          ring
        · rw [sq_abs]
      have hmul := mul_le_mul_of_nonneg_right hcoef'
        (by positivity : 0 ≤ (Real.sqrt Real.pi)⁻¹ *
          Real.exp (-(1 / 4 : ℝ) * y ^ 2) * |y| ^ alpha * (1 / 2 : ℝ))
      have hexp : -(1 / 4 : ℝ) * y ^ 2 = y ^ 2 * (-1 / 4 : ℝ) := by ring
      rw [hexp] at hmul
      nlinarith [hmul]

  let F : ℝ → ℝ := fun x => |iteratedDeriv 2 (gaussianHeatKernel 1) x| * |x| ^ alpha
  let C : ℝ := 1 + ∫ y : ℝ, F y
  have hF_nonneg : 0 ≤ ∫ y : ℝ, F y := integral_nonneg (fun y => by positivity)
  have hCpos : 0 < C := by dsimp [C]; linarith

  refine ⟨C, hCpos, ?_⟩
  intro t ht
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt
  let G : ℝ → ℝ := fun x => |iteratedDeriv 2 (gaussianHeatKernel t) x| * |x| ^ alpha
  have hscale : ∀ y : ℝ, G (Real.sqrt t * y) =
      t ^ (alpha / 2 - 3 / 2) * F y := by
    intro y
    have hderiv := gaussianHeatKernel_derivatives ht
    have hess : iteratedDeriv 2 (gaussianHeatKernel t) (Real.sqrt t * y) =
        gaussianHeatHessian t (Real.sqrt t * y) := (hderiv.2 _).2.1
    dsimp [G]
    rw [hess]
    unfold gaussianHeatHessian gaussianHeatKernel F
    have hess1 : iteratedDeriv 2 (gaussianHeatKernel 1) y =
        gaussianHeatHessian 1 y :=
      ((gaussianHeatKernel_derivatives (t := (1 : ℝ)) (by norm_num)).2 y).2.1
    rw [hess1]
    unfold gaussianHeatHessian gaussianHeatKernel
    have hsqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
    have hroot_nonneg : 0 ≤ Real.sqrt t := hsqrt.le
    have hfour : 4 * Real.pi * t > 0 := by positivity
    have hroot4 : Real.sqrt (4 * Real.pi * t) =
        Real.sqrt t * Real.sqrt (4 * Real.pi) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (4 : ℝ) * Real.pi), Real.sqrt_mul (by positivity)]
      ring
    rw [hroot4]
    have hyabs : |Real.sqrt t * y| = Real.sqrt t * |y| := by
      rw [abs_mul, abs_of_nonneg hroot_nonneg]
    rw [hyabs, Real.mul_rpow hroot_nonneg (abs_nonneg y)]
    simp only [mul_pow]
    rw [hsqrt_sq]
    field_simp [hsqrt_ne]
    rw [show (alpha - 3) / 2 = alpha / 2 - 3 / 2 by ring]
    rw [Real.rpow_sub ht (alpha / 2) (3 / 2)]
    rw [Real.rpow_div_two_eq_sqrt 3 ht.le]
    simp only [abs_div]
    have hden1 : 0 < t * 4 * 2 * Real.sqrt t * Real.sqrt (4 * Real.pi) := by positivity
    have hden2 : 0 < (4 : ℝ) * 2 * Real.sqrt (4 * Real.pi) := by positivity
    rw [abs_of_pos hden1, abs_of_pos hden2]
    field_simp [hsqrt_ne]
    ring_nf
    have hpowα : t ^ (alpha * (1 / 2 : ℝ)) = (Real.sqrt t) ^ alpha := by
      rw [show alpha * (1 / 2 : ℝ) = alpha / 2 by ring,
        Real.rpow_div_two_eq_sqrt alpha ht.le]
    have hpow3 : (Real.sqrt t) ^ 3 = t * Real.sqrt t := by
      calc
        (Real.sqrt t) ^ 3 = (Real.sqrt t) ^ 2 * Real.sqrt t := by ring
        _ = t * Real.sqrt t := by rw [hsqrt_sq]
    rw [hpowα]
    have halg : ∀ a b q : ℝ,
        a * q * b * (Real.sqrt t) ^ 3 = a * b * (t * Real.sqrt t) * q := by
      intro a b q
      calc
        a * q * b * (Real.sqrt t) ^ 3 =
            a * q * b * ((Real.sqrt t) ^ 2 * Real.sqrt t) := by ring
        _ = a * q * b * (t * Real.sqrt t) := by rw [hsqrt_sq]
        _ = a * b * (t * Real.sqrt t) * q := by ring
    have hA :
        |y ^ 2 * Real.exp (y ^ 2 * (-1 / 4 : ℝ)) * 2 -
            Real.exp (y ^ 2 * (-1 / 4 : ℝ)) * 4| =
          |y ^ 2 * (2 * Real.exp (y ^ 2 * (-1 / 4 : ℝ))) -
            4 * Real.exp (y ^ 2 * (-1 / 4 : ℝ))| := by
      congr 1
      ring
    have hgen := halg
      |y ^ 2 * Real.exp (y ^ 2 * (-1 / 4 : ℝ)) * 2 -
          Real.exp (y ^ 2 * (-1 / 4 : ℝ)) * 4|
      (|y| ^ alpha) ((Real.sqrt t) ^ alpha)
    rw [hA] at hgen
    rw [hA]
    convert hgen using 1
    · simp
    · simp [mul_assoc]
  have hGcomp : Integrable (fun y => G (Real.sqrt t * y)) volume := by
    rw [show (fun y => G (Real.sqrt t * y)) =
        (fun y => t ^ (alpha / 2 - 3 / 2) * F y) by
          funext y; rw [hscale y]]
    exact hkernel1.const_mul _
  have hG : Integrable G volume :=
    (integrable_comp_smul_iff volume G hsqrt_ne).mp hGcomp
  refine ⟨hG, ?_⟩
  have hcomp_int : (∫ y : ℝ, G (Real.sqrt t * y)) =
      (Real.sqrt t)⁻¹ * ∫ x : ℝ, G x := by
    simpa [smul_eq_mul, abs_of_pos hsqrt] using
      (Measure.integral_comp_mul_left G (Real.sqrt t))
  have hcomp_scale : (∫ y : ℝ, G (Real.sqrt t * y)) =
      t ^ (alpha / 2 - 3 / 2) * ∫ y : ℝ, F y := by
    rw [show (fun y => G (Real.sqrt t * y)) =
        (fun y => t ^ (alpha / 2 - 3 / 2) * F y) by
          funext y; rw [hscale y], integral_const_mul]
  have hG_integral : (∫ x : ℝ, G x) =
      Real.sqrt t * (t ^ (alpha / 2 - 3 / 2) * ∫ y : ℝ, F y) := by
    rw [hcomp_scale] at hcomp_int
    field_simp [hsqrt_ne] at hcomp_int
    calc
      (∫ x : ℝ, G x) =
          (t ^ (alpha / 2 - 3 / 2) * ∫ y : ℝ, F y) * Real.sqrt t :=
        by
          convert hcomp_int.symm using 1
          ring
      _ = Real.sqrt t * (t ^ (alpha / 2 - 3 / 2) * ∫ y : ℝ, F y) := by ring
  rw [show (∫ x : ℝ, |iteratedDeriv 2 (gaussianHeatKernel t) x| * |x| ^ alpha) =
      ∫ x : ℝ, G x by rfl, hG_integral]
  dsimp [C]
  have ht_rpow : t ^ (alpha / 2 - 1) =
      Real.sqrt t * t ^ (alpha / 2 - 3 / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [ht_rpow]
  calc
    Real.sqrt t * (t ^ (alpha / 2 - 3 / 2) * ∫ y : ℝ, F y) =
        (Real.sqrt t * t ^ (alpha / 2 - 3 / 2)) * ∫ y : ℝ, F y := by ring
    _ ≤ (Real.sqrt t * t ^ (alpha / 2 - 3 / 2)) * (1 + ∫ y : ℝ, F y) := by
      gcongr
      linarith
    _ = (1 + ∫ y : ℝ, F y) * (Real.sqrt t * t ^ (alpha / 2 - 3 / 2)) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
