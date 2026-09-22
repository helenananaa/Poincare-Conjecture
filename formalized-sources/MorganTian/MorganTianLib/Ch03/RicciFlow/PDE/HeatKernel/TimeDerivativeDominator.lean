import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ActualHeatTimeFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TimeSpaceGaussianBound
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianEstimate
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideHessianUnweighted
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatTimeDerivativeL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalInitialTrace
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ShiftedDerivativeDominator
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Local positive-time domination of the kernel and its actual time derivative. -/
theorem euclideanHeatKernel_time_derivative_dominator (a b R : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hR : 0 ≤ R) :
    ∃ g : E3 → ℝ, Integrable g volume ∧ (∀ y, 0 ≤ g y) ∧
      ∀ (t : ℝ) (x y : E3), t ∈ Icc a b → ‖x‖ ≤ R →
        |euclideanHeatKernel 3 t (x-y)| ≤ g y ∧
        |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| ≤ g y :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, hcompare⟩ :=
    euclideanHeatKernel_compact_time_space_bound a b R ha hab hR
  obtain ⟨C0, hC0, hmoment0⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (0 : ℝ) (by norm_num)
  obtain ⟨C2, hC2, hmoment2⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (2 : ℝ) (by norm_num)
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h0 : Integrable
      (fun y : E3 => euclideanHeatKernel 3 (2 * b) y) volume := by
    simpa using (hmoment0 (2 * b) (by positivity)).1
  have h2 : Integrable
      (fun y : E3 => euclideanHeatKernel 3 (2 * b) y * ‖y‖ ^ (2 : ℕ)) volume := by
    convert (hmoment2 (2 * b) (by positivity)).1 using 1 <;>
      norm_num [Real.rpow_two]
  let D : ℝ := 1 + R ^ 2 / (2 * a ^ 2) + 1 / (2 * a ^ 2) + 3 / (2 * a)
  let g : E3 → ℝ := fun y =>
    C * D * (euclideanHeatKernel 3 (2 * b) y +
      euclideanHeatKernel 3 (2 * b) y * ‖y‖ ^ (2 : ℕ))
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hD1 : 1 ≤ D := by
    dsimp [D]
    have h₁ : 0 ≤ R ^ 2 / (2 * a ^ 2) := by positivity
    have h₂ : 0 ≤ 1 / (2 * a ^ 2) := by positivity
    have h₃ : 0 ≤ 3 / (2 * a) := by positivity
    linarith
  have hg : Integrable g volume := by
    dsimp [g]
    exact (h0.add h2).const_mul _
  have hK2 (y : E3) : 0 ≤ euclideanHeatKernel 3 (2 * b) y := by
    exact (euclideanHeatKernel_pos 3 (by positivity) y).le
  have hg_nonneg : ∀ y, 0 ≤ g y := by
    intro y
    dsimp [g]
    have hn : 0 ≤ ‖y‖ ^ (2 : ℕ) := by positivity
    exact mul_nonneg (mul_nonneg hC.le hD.le)
      (add_nonneg (hK2 y) (mul_nonneg (hK2 y) hn))
  have hnormsq (x y : E3) (hxy : ‖x‖ ≤ R) :
      ‖x - y‖ ^ 2 ≤ 2 * R ^ 2 + 2 * ‖y‖ ^ 2 := by
    have hnorm : ‖x - y‖ ≤ R + ‖y‖ := by
      calc
        ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ R + ‖y‖ := by
          simpa [add_comm] using add_le_add_left hxy ‖y‖
    have hprod : 0 ≤ (R + ‖y‖ - ‖x - y‖) *
        (R + ‖y‖ + ‖x - y‖) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr hnorm
      · positivity
    nlinarith [sq_nonneg (R - ‖y‖)]
  have hcoef_bound (t : ℝ) (x y : E3) (ht : t ∈ Icc a b)
      (hxy : ‖x‖ ≤ R) :
      ‖x - y‖ ^ 2 / (4 * t ^ 2) + 3 / (2 * t) ≤
        D * (1 + ‖y‖ ^ (2 : ℕ)) := by
    have hta : 0 < t := lt_of_lt_of_le ha ht.1
    let A : ℝ := R ^ 2 / (2 * a ^ 2) + 3 / (2 * a)
    let B : ℝ := 1 / (2 * a ^ 2)
    have hquad : ‖x - y‖ ^ 2 / (4 * t ^ 2) + 3 / (2 * t) ≤
        A + B * ‖y‖ ^ (2 : ℕ) := by
      have hdiv : ‖x - y‖ ^ 2 / (4 * t ^ 2) ≤
          (2 * R ^ 2 + 2 * ‖y‖ ^ 2) / (4 * t ^ 2) :=
        div_le_div_of_nonneg_right (hnormsq x y hxy) (by positivity)
      have htime1 : 1 / t ≤ 1 / a := by
        exact (one_div_le_one_div_of_le ha ht.1)
      have htime2 : 1 / t ^ 2 ≤ 1 / a ^ 2 := by
        apply one_div_le_one_div_of_le (sq_pos_of_pos ha)
        have hp : 0 ≤ (t - a) * (t + a) := by
          exact mul_nonneg (sub_nonneg.mpr ht.1) (by positivity)
        nlinarith
      have hdiv' : (2 * R ^ 2 + 2 * ‖y‖ ^ 2) / (4 * t ^ 2) ≤
          R ^ 2 / (2 * a ^ 2) + ‖y‖ ^ 2 / (2 * a ^ 2) := by
        calc
          (2 * R ^ 2 + 2 * ‖y‖ ^ 2) / (4 * t ^ 2) =
              (R ^ 2 + ‖y‖ ^ 2) / 2 * (1 / t ^ 2) := by field_simp; ring
          _ ≤ (R ^ 2 + ‖y‖ ^ 2) / 2 * (1 / a ^ 2) := by
            exact mul_le_mul_of_nonneg_left htime2 (by positivity)
          _ = R ^ 2 / (2 * a ^ 2) + ‖y‖ ^ 2 / (2 * a ^ 2) := by ring
      have htime3 : 3 / (2 * t) ≤ 3 / (2 * a) := by
        calc
          3 / (2 * t) = (3 / 2) * (1 / t) := by ring
          _ ≤ (3 / 2) * (1 / a) :=
            mul_le_mul_of_nonneg_left htime1 (by norm_num)
          _ = 3 / (2 * a) := by ring
      have hadd := add_le_add hdiv htime3
      have hadd' : ‖x - y‖ ^ 2 / (4 * t ^ 2) + 3 / (2 * t) ≤
          (R ^ 2 / (2 * a ^ 2) + ‖y‖ ^ 2 / (2 * a ^ 2)) + 3 / (2 * a) :=
        hadd.trans (add_le_add hdiv' (le_refl _))
      dsimp [A, B]
      exact hadd'.trans_eq (by ring)
    have hA : A ≤ D := by
      dsimp [A, D]
      have h₁ : 0 ≤ (1 : ℝ) := by norm_num
      have h₂ : 0 ≤ 1 / (2 * a ^ 2) := by positivity
      linarith
    have hB : B ≤ D := by
      dsimp [A, B, D]
      have h₁ : 0 ≤ (1 : ℝ) := by norm_num
      have h₂ : 0 ≤ R ^ 2 / (2 * a ^ 2) := by positivity
      have h₃ : 0 ≤ 3 / (2 * a) := by positivity
      linarith
    have hsum : A + B * ‖y‖ ^ (2 : ℕ) ≤
        D + D * ‖y‖ ^ (2 : ℕ) := by
      exact add_le_add hA (mul_le_mul_of_nonneg_right hB (by positivity))
    exact hquad.trans (by simpa [mul_add, add_mul] using hsum)
  have hmuldom (t : ℝ) (x y : E3) (ht : t ∈ Icc a b)
      (hxy : ‖x‖ ≤ R) (q : ℝ) (hq : 0 ≤ q)
      (hqD : q ≤ D * (1 + ‖y‖ ^ (2 : ℕ))) :
      q * euclideanHeatKernel 3 t (x - y) ≤ g y := by
    have hbase := mul_le_mul_of_nonneg_left (hcompare t x y ht hxy) hq
    have hcoef := mul_le_mul_of_nonneg_right hqD
      (mul_nonneg hC.le (hK2 y))
    calc
      q * euclideanHeatKernel 3 t (x - y) ≤
          q * (C * euclideanHeatKernel 3 (2 * b) y) := hbase
      _ ≤ (D * (1 + ‖y‖ ^ (2 : ℕ))) *
          (C * euclideanHeatKernel 3 (2 * b) y) := hcoef
      _ = g y := by
        dsimp [g]
        ring
  refine ⟨g, hg, hg_nonneg, ?_⟩
  intro t x y ht hxy
  have hta : 0 < t := lt_of_lt_of_le ha ht.1
  have hKt : 0 ≤ euclideanHeatKernel 3 t (x - y) :=
    (euclideanHeatKernel_pos 3 hta (x - y)).le
  have hone : (1 : ℝ) ≤ D * (1 + ‖y‖ ^ (2 : ℕ)) := by
    calc
      (1 : ℝ) ≤ D := hD1
      _ ≤ D * (1 + ‖y‖ ^ (2 : ℕ)) := by
        nlinarith [mul_nonneg hD.le (sq_nonneg ‖y‖)]
  have hkernel : |euclideanHeatKernel 3 t (x - y)| ≤ g y := by
    rw [abs_of_nonneg hKt]
    simpa only [one_mul] using hmuldom t x y ht hxy 1 (by norm_num) hone
  have hderiv : deriv (fun s => euclideanHeatKernel 3 s (x - y)) t =
      (‖x - y‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) *
        euclideanHeatKernel 3 t (x - y) :=
    (euclideanHeatKernel_three_time_formula hta (x - y)).deriv
  have hcoef :
      |‖x - y‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)| ≤
        ‖x - y‖ ^ 2 / (4 * t ^ 2) + 3 / (2 * t) := by
    calc
      |‖x - y‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)| ≤
          |‖x - y‖ ^ 2 / (4 * t ^ 2)| + |3 / (2 * t)| := by
        simpa [abs_neg] using
          (abs_sub_le (‖x - y‖ ^ 2 / (4 * t ^ 2)) 0 (3 / (2 * t)))
      _ = ‖x - y‖ ^ 2 / (4 * t ^ 2) + 3 / (2 * t) := by
        rw [abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
  have hderiv_bound :
      |deriv (fun s => euclideanHeatKernel 3 s (x - y)) t| ≤ g y := by
    rw [hderiv, abs_mul, abs_of_nonneg hKt]
    exact hmuldom t x y ht hxy _ (abs_nonneg _) 
      (hcoef.trans (hcoef_bound t x y ht hxy))
  exact ⟨hkernel, hderiv_bound⟩
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
