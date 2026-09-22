import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Weighted L1 Hessian control assembled from formula and Gaussian moments. -/
theorem euclideanHeatKernel_three_weighted_hessian_recursive (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ i j : Fin 3,
      Integrable (fun y : E3 =>
        |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)| * ‖y‖^alpha) volume ∧
      (∫ y : E3, |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)| * ‖y‖^alpha) ≤
        C*t^(alpha/2-1) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C0, hC0, hmoment0⟩ :=
    euclideanHeatKernel_three_nonnegative_moment alpha ha.le
  obtain ⟨C2, hC2, hmoment2⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (alpha + 2) (by linarith)
  let C : ℝ := C2 / 4 + C0 / 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht i j
  let G : E3 → ℝ := fun y =>
    (1 / (4 * t ^ 2)) *
        (euclideanHeatKernel 3 t y * ‖y‖ ^ (alpha + 2)) +
      (1 / (2 * t)) * (euclideanHeatKernel 3 t y * ‖y‖ ^ alpha)
  have hG : Integrable G volume := by
    dsimp [G]
    exact (hmoment2 t ht).1.const_mul _ |>.add
      ((hmoment0 t ht).1.const_mul _)
  have hKcont : Continuous (fun y : E3 => euclideanHeatKernel 3 t y) := by
    unfold euclideanHeatKernel
    exact (contDiff_prod (fun k _ =>
      (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
  have hentry_cont : Continuous
      (fun y : E3 => fderiv ℝ (fun z : E3 =>
        fderiv ℝ (euclideanHeatKernel 3 t) z (EuclideanSpace.single i 1)) y
          (EuclideanSpace.single j 1)) := by
    have hformula :
        (fun y : E3 => fderiv ℝ (fun z : E3 =>
          fderiv ℝ (euclideanHeatKernel 3 t) z (EuclideanSpace.single i 1)) y
            (EuclideanSpace.single j 1)) =
          (fun y : E3 =>
            (y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) *
              euclideanHeatKernel 3 t y) := by
      funext y
      exact euclideanHeatKernel_three_hessian_formula ht y i j
    rw [hformula]
    have hcoef : Continuous
        (fun y : E3 => y i * y j / (4 * t ^ 2) -
          (if i = j then 1 / (2 * t) else 0)) := by
      fun_prop
    exact hcoef.mul hKcont
  have htarget_meas : Measurable
      (fun y : E3 =>
        |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)| * ‖y‖^alpha) := by
    exact (hentry_cont.abs.mul
      (continuous_norm.rpow_const (fun _ => Or.inr ha.le))).measurable
  have hpoint : ∀ y : E3, (fun y : E3 =>
        |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)| * ‖y‖^alpha) y
      ≤ G y := by
    intro y
    have hyi : |y i| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y i)
    have hyj : |y j| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y j)
    have hprod : |y i * y j| ≤ ‖y‖ ^ 2 := by
      rw [abs_mul]
      exact (mul_le_mul hyi hyj (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)
    have hden : 0 < 4 * t ^ 2 := by positivity
    have hdiag : |(if i = j then 1 / (2 * t) else 0)| ≤ 1 / (2 * t) := by
      by_cases hij : i = j
      · rw [if_pos hij, abs_of_pos (by positivity : 0 < (1 : ℝ) / (2 * t))]
      · rw [if_neg hij, abs_zero]
        positivity
    have hcoef :
        |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| ≤
          ‖y‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
      calc
        |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| ≤
            |y i * y j / (4 * t ^ 2)| +
              |(if i = j then 1 / (2 * t) else 0)| :=
          by
            simpa [abs_neg] using
              (abs_sub_le (y i * y j / (4 * t ^ 2)) (0 : ℝ)
                (if i = j then 1 / (2 * t) else 0))
        _ = |y i * y j| / (4 * t ^ 2) +
              |(if i = j then 1 / (2 * t) else 0)| := by
          rw [abs_div, abs_of_pos hden]
        _ ≤ ‖y‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
          exact add_le_add (div_le_div_of_nonneg_right hprod hden.le) hdiag
    change |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)| * ‖y‖^alpha ≤ G y
    rw [euclideanHeatKernel_three_hessian_formula ht y i j, abs_mul,
      abs_of_nonneg (euclideanHeatKernel_pos 3 ht y).le]
    have hmul :
        (|y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| *
            euclideanHeatKernel 3 t y) * ‖y‖ ^ alpha ≤
          ((‖y‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) *
            euclideanHeatKernel 3 t y) * ‖y‖ ^ alpha :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (euclideanHeatKernel_pos 3 ht y).le)
        (Real.rpow_nonneg (norm_nonneg y) alpha)
    calc
      |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| *
          euclideanHeatKernel 3 t y * ‖y‖ ^ alpha ≤
          (‖y‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) *
            euclideanHeatKernel 3 t y * ‖y‖ ^ alpha := hmul
      _ = G y := by
        dsimp [G]
        have hden2 : 1 / (4 * t ^ 2) = t⁻¹ ^ 2 / 4 := by
          field_simp [ht.ne']
        have hden1 : 1 / (2 * t) = t⁻¹ / 2 := by
          field_simp [ht.ne']
        rw [hden2, hden1, Real.rpow_add' (norm_nonneg y) (by linarith)]
        field_simp [ht.ne'] <;>
          simp only [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm,
            add_assoc, add_left_comm, add_comm]
        rw [mul_comm (‖y‖ ^ 2) (‖y‖ ^ alpha)]
        simp
  have htarget : Integrable (fun y : E3 =>
      |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)| * ‖y‖^alpha) volume :=
    by
      refine hG.mono' htarget_meas.aestronglyMeasurable ?_
      filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hpoint y
      · exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg y) _)
  have hG_int : (∫ y : E3, G y) =
      (1 / (4 * t ^ 2)) *
          (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖ ^ (alpha + 2)) +
        (1 / (2 * t)) *
          (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖ ^ alpha) := by
    dsimp [G]
    rw [integral_add ((hmoment2 t ht).1.const_mul _)
        ((hmoment0 t ht).1.const_mul _),
      integral_const_mul, integral_const_mul]
  have hpow2 :
      t ^ ((alpha + 2) / 2) / t ^ (2 : ℕ) = t ^ (alpha / 2 - 1) := by
    calc
      t ^ ((alpha + 2) / 2) / t ^ (2 : ℕ) =
          t ^ ((alpha + 2) / 2) / t ^ (2 : ℝ) := by
            norm_num [Real.rpow_natCast]
      _ = t ^ ((alpha + 2) / 2 - 2) := by
            rw [← Real.rpow_sub ht]
      _ = t ^ (alpha / 2 - 1) := by congr 1 <;> ring
  have hpow0 : t ^ (alpha / 2) / t = t ^ (alpha / 2 - 1) := by
    have ht1 : t ^ (1 : ℝ) = t := Real.rpow_one t
    calc
      t ^ (alpha / 2) / t = t ^ (alpha / 2) / t ^ (1 : ℝ) := by rw [ht1]
      _ = t ^ (alpha / 2 - 1) := by rw [← Real.rpow_sub ht]
  have hscale2 :
      (1 / (4 * t ^ 2)) * (C2 * t ^ ((alpha + 2) / 2)) =
        (C2 / 4) * t ^ (alpha / 2 - 1) := by
    calc
      (1 / (4 * t ^ 2)) * (C2 * t ^ ((alpha + 2) / 2)) =
          (C2 / 4) * (t ^ ((alpha + 2) / 2) / t ^ (2 : ℕ)) := by
            field_simp [ht.ne']
      _ = (C2 / 4) * t ^ (alpha / 2 - 1) := by rw [hpow2]
  have hscale0 :
      (1 / (2 * t)) * (C0 * t ^ (alpha / 2)) =
        (C0 / 2) * t ^ (alpha / 2 - 1) := by
    calc
      (1 / (2 * t)) * (C0 * t ^ (alpha / 2)) =
          (C0 / 2) * (t ^ (alpha / 2) / t) := by
            field_simp [ht.ne']
      _ = (C0 / 2) * t ^ (alpha / 2 - 1) := by rw [hpow0]
  refine ⟨htarget, ?_⟩
  have hle :
      (∫ y : E3, |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)| * ‖y‖^alpha) ≤
        ∫ y : E3, G y :=
    integral_mono htarget hG (fun y => hpoint y)
  rw [hG_int] at hle
  calc
    (∫ y : E3, |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)| * ‖y‖^alpha) ≤
        (1 / (4 * t ^ 2)) * (C2 * t ^ ((alpha + 2) / 2)) +
          (1 / (2 * t)) * (C0 * t ^ (alpha / 2)) := by
      exact hle.trans (add_le_add
        (mul_le_mul_of_nonneg_left (hmoment2 t ht).2 (by positivity))
        (mul_le_mul_of_nonneg_left (hmoment0 t ht).2 (by positivity)))
    _ = C * t ^ (alpha / 2 - 1) := by
      dsimp [C]
      rw [hscale2, hscale0]
      ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
