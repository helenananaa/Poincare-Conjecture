import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ShiftedGaussianBound
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
/-- One integrable majorant controls all actual kernel derivatives up to order two locally in x. -/
theorem euclideanHeatKernel_three_shifted_derivative_dominator (t R : ℝ)
    (ht : 0 < t) (hR : 0 ≤ R) :
    ∃ g : E3 → ℝ, Integrable g volume ∧ (∀ y, 0 ≤ g y) ∧
      ∀ x y : E3, ‖x‖ ≤ R →
        |euclideanHeatKernel 3 t (x-y)| ≤ g y ∧
        (∀ i : Fin 3, |fderiv ℝ (euclideanHeatKernel 3 t) (x-y) (EuclideanSpace.single i 1)| ≤ g y) ∧
        (∀ i j : Fin 3, |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)| ≤ g y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, hshift⟩ :=
    euclideanHeatKernel_three_shifted_bound t R ht hR
  obtain ⟨C0, hC0, hmoment0⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (0 : ℝ) (by norm_num)
  obtain ⟨C2, hC2, hmoment2⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (2 : ℝ) (by norm_num)
  let D : ℝ :=
    1 + (R + 1) / (2 * t) + (R ^ 2 / (2 * t ^ 2) + 1 / (2 * t)) +
      1 / (2 * t ^ 2)
  let g : E3 → ℝ := fun y =>
    C * D * (euclideanHeatKernel 3 (2 * t) y +
      euclideanHeatKernel 3 (2 * t) y * ‖y‖ ^ (2 : ℕ))
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hD1 : 1 ≤ D := by
    dsimp [D]
    have h₁ : 0 ≤ (R + 1) / (2 * t) := by positivity
    have h₂ : 0 ≤ R ^ 2 / (2 * t ^ 2) + 1 / (2 * t) := by positivity
    have h₃ : 0 ≤ 1 / (2 * t ^ 2) := by positivity
    linarith
  have hK2 (y : E3) : 0 ≤ euclideanHeatKernel 3 (2 * t) y := by
    exact (euclideanHeatKernel_pos 3 (by positivity) y).le
  have h0 : Integrable (fun y : E3 => euclideanHeatKernel 3 (2 * t) y) volume := by
    simpa using (hmoment0 (2 * t) (by positivity)).1
  have h2 : Integrable
      (fun y : E3 => euclideanHeatKernel 3 (2 * t) y * ‖y‖ ^ (2 : ℕ)) volume := by
    convert (hmoment2 (2 * t) (by positivity)).1 using 1 <;>
      norm_num [Real.rpow_two]
  have hg : Integrable g volume := by
    dsimp [g]
    exact (h0.add h2).const_mul _
  have hg_nonneg : ∀ y, 0 ≤ g y := by
    intro y
    dsimp [g]
    have hk := hK2 y
    have hn : 0 ≤ ‖y‖ ^ (2 : ℕ) := by positivity
    exact mul_nonneg (mul_nonneg hC.le hD.le)
      (add_nonneg hk (mul_nonneg hk hn))
  have hdom (x y : E3) (a : ℝ) (ha : 0 ≤ a)
      (haD : a ≤ D * (1 + ‖y‖ ^ (2 : ℕ)))
      (hxy : ‖x‖ ≤ R) :
      a * euclideanHeatKernel 3 t (x - y) ≤ g y := by
    have hxy' := hshift x y hxy
    have hbase : a * euclideanHeatKernel 3 t (x - y) ≤
        a * (C * euclideanHeatKernel 3 (2 * t) y) :=
      mul_le_mul_of_nonneg_left hxy' ha
    have hcoef : a * (C * euclideanHeatKernel 3 (2 * t) y) ≤
        (D * (1 + ‖y‖ ^ (2 : ℕ))) *
          (C * euclideanHeatKernel 3 (2 * t) y) :=
      mul_le_mul_of_nonneg_right haD
        (mul_nonneg hC.le (hK2 y))
    calc
      a * euclideanHeatKernel 3 t (x - y) ≤
          a * (C * euclideanHeatKernel 3 (2 * t) y) := hbase
      _ ≤ (D * (1 + ‖y‖ ^ (2 : ℕ))) *
          (C * euclideanHeatKernel 3 (2 * t) y) := hcoef
      _ = g y := by
        dsimp [g]
        ring
  have hnormxy (x y : E3) (hxy : ‖x‖ ≤ R) :
      ‖x - y‖ ≤ R + ‖y‖ := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ R + ‖y‖ := by
        simpa [add_comm] using add_le_add_left hxy ‖y‖
  have hnormsq (x y : E3) (hxy : ‖x‖ ≤ R) :
      ‖x - y‖ ^ 2 ≤ 2 * R ^ 2 + 2 * ‖y‖ ^ 2 := by
    have hxy' := hnormxy x y hxy
    have hprod : 0 ≤ (R + ‖y‖ - ‖x - y‖) *
        (R + ‖y‖ + ‖x - y‖) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr hxy'
      · positivity
    nlinarith [sq_nonneg (R - ‖y‖)]
  have hpoly_grad (x y : E3) (hxy : ‖x‖ ≤ R) :
      |(x - y : E3) 0| / (2 * t) ≤ D * (1 + ‖y‖ ^ (2 : ℕ)) := by
    have hi : |(x - y : E3) 0| ≤ R + ‖y‖ := by
      have hi' : |(x - y : E3) 0| ≤ ‖x - y‖ := by
        simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (x - y) 0)
      exact hi'.trans (hnormxy x y hxy)
    have hn : ‖y‖ ≤ 1 + ‖y‖ ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (‖y‖ - 1)]
    have hRpoly : R + ‖y‖ ≤ (R + 1) * (1 + ‖y‖ ^ (2 : ℕ)) := by
      nlinarith [mul_nonneg hR (sq_nonneg ‖y‖)]
    have hfirst : |(x - y : E3) 0| / (2 * t) ≤
        ((R + 1) / (2 * t)) * (1 + ‖y‖ ^ (2 : ℕ)) := by
      apply (div_le_iff₀ (by positivity)).2
      calc
        |(x - y : E3) 0| ≤ R + ‖y‖ := hi
        _ ≤ (R + 1) * (1 + ‖y‖ ^ (2 : ℕ)) := hRpoly
        _ = ((R + 1) / (2 * t)) *
            (1 + ‖y‖ ^ (2 : ℕ)) * (2 * t) := by
          field_simp
    have hDgrad : (R + 1) / (2 * t) ≤ D := by
      dsimp [D]
      have h₁ : 0 ≤ 1 := by norm_num
      have h₂ : 0 ≤ R ^ 2 / (2 * t ^ 2) + 1 / (2 * t) := by positivity
      have h₃ : 0 ≤ 1 / (2 * t ^ 2) := by positivity
      linarith
    exact hfirst.trans (mul_le_mul_of_nonneg_right hDgrad (by positivity))
  have hpoly_hess (x y : E3) (hxy : ‖x‖ ≤ R) :
      ‖x - y‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t) ≤
        D * (1 + ‖y‖ ^ (2 : ℕ)) := by
    let q0 : ℝ := R ^ 2 / (2 * t ^ 2) + 1 / (2 * t)
    let q2 : ℝ := 1 / (2 * t ^ 2)
    have hquad : ‖x - y‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t) ≤
        q0 + q2 * ‖y‖ ^ (2 : ℕ) := by
      have hdiv := div_le_div_of_nonneg_right (hnormsq x y hxy)
        (by positivity : 0 ≤ 4 * t ^ 2)
      have heq : (2 * R ^ 2 + 2 * ‖y‖ ^ 2) / (4 * t ^ 2) + 1 / (2 * t) =
          q0 + q2 * ‖y‖ ^ (2 : ℕ) := by
        dsimp [q0, q2]
        field_simp
        ring
      have hadd := add_le_add_left hdiv (1 / (2 * t))
      have hadd' : ‖x - y‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t) ≤
          (2 * R ^ 2 + 2 * ‖y‖ ^ 2) / (4 * t ^ 2) + 1 / (2 * t) := by
        simpa [add_comm] using hadd
      exact hadd'.trans_eq heq
    have hq0 : 0 ≤ q0 := by
      dsimp [q0]
      positivity
    have hq2 : 0 ≤ q2 := by
      dsimp [q2]
      positivity
    have hq0D : q0 ≤ D := by
      dsimp [q0, D]
      have h₁ : 0 ≤ 1 + (R + 1) / (2 * t) := by positivity
      have h₂ : 0 ≤ 1 / (2 * t ^ 2) := by positivity
      linarith
    have hq2D : q2 ≤ D := by
      dsimp [q2, D]
      have h₁ : 0 ≤ 1 + (R + 1) / (2 * t) := by positivity
      have h₂ : 0 ≤ R ^ 2 / (2 * t ^ 2) + 1 / (2 * t) := by positivity
      linarith
    have hsum : q0 + q2 * ‖y‖ ^ (2 : ℕ) ≤
        D + D * ‖y‖ ^ (2 : ℕ) := by
      exact add_le_add hq0D
        (mul_le_mul_of_nonneg_right hq2D (by positivity))
    exact hquad.trans (by simpa [mul_add, add_mul] using hsum)
  refine ⟨g, hg, hg_nonneg, ?_⟩
  intro x y hxy
  have hK : euclideanHeatKernel 3 t (x - y) ≤
      C * euclideanHeatKernel 3 (2 * t) y := hshift x y hxy
  have hKpos : 0 ≤ euclideanHeatKernel 3 t (x - y) :=
    (euclideanHeatKernel_pos 3 ht (x - y)).le
  have hone : (1 : ℝ) ≤ D * (1 + ‖y‖ ^ (2 : ℕ)) := by
    calc
      (1 : ℝ) ≤ D := hD1
      _ ≤ D * (1 + ‖y‖ ^ (2 : ℕ)) := by
        nlinarith [mul_nonneg hD.le (sq_nonneg ‖y‖)]
  have hkernel : |euclideanHeatKernel 3 t (x - y)| ≤ g y := by
    rw [abs_of_nonneg hKpos]
    simpa using hdom x y 1 (by norm_num) hone hxy
  have hgrad (i : Fin 3) :
      |fderiv ℝ (euclideanHeatKernel 3 t) (x-y)
          (EuclideanSpace.single i 1)| ≤ g y := by
    have hi : |(x - y : E3) i| ≤ ‖x - y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (x - y) i)
    have ha : 0 ≤ |(x - y : E3) i| / (2 * t) := by positivity
    have haD : |(x - y : E3) i| / (2 * t) ≤
        D * (1 + ‖y‖ ^ (2 : ℕ)) := by
      calc
        |(x - y : E3) i| / (2 * t) ≤ ‖x - y‖ / (2 * t) :=
          div_le_div_of_nonneg_right hi (by positivity)
        _ ≤ (R + ‖y‖) / (2 * t) :=
          div_le_div_of_nonneg_right (hnormxy x y hxy) (by positivity)
        _ ≤ D * (1 + ‖y‖ ^ (2 : ℕ)) := by
          have hRpoly : R + ‖y‖ ≤ (R + 1) *
              (1 + ‖y‖ ^ (2 : ℕ)) := by
            nlinarith [mul_nonneg hR (sq_nonneg ‖y‖)]
          have hfirst : (R + ‖y‖) / (2 * t) ≤
              ((R + 1) / (2 * t)) * (1 + ‖y‖ ^ (2 : ℕ)) := by
            apply (div_le_iff₀ (by positivity)).2
            calc
              R + ‖y‖ ≤ (R + 1) * (1 + ‖y‖ ^ (2 : ℕ)) := hRpoly
              _ = ((R + 1) / (2 * t)) *
                  (1 + ‖y‖ ^ (2 : ℕ)) * (2 * t) := by
                field_simp
          exact hfirst.trans (mul_le_mul_of_nonneg_right
            (by
              dsimp [D]
              have h₁ : 0 ≤ 1 := by norm_num
              have h₂ : 0 ≤ R ^ 2 / (2 * t ^ 2) + 1 / (2 * t) := by positivity
              have h₃ : 0 ≤ 1 / (2 * t ^ 2) := by positivity
              linarith) (by positivity))
    rw [euclideanHeatKernel_three_gradient_formula ht (x-y) i,
      abs_mul, abs_neg, abs_div,
      abs_of_pos (show 0 < 2 * t by positivity),
      abs_of_nonneg hKpos]
    exact hdom x y _ ha haD hxy
  have hhess (i j : Fin 3) :
      |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)| ≤ g y := by
    have hi : |(x - y : E3) i| ≤ ‖x - y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (x - y) i)
    have hj : |(x - y : E3) j| ≤ ‖x - y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (x - y) j)
    have hprod : |(x - y : E3) i * (x - y : E3) j| ≤
        ‖x - y‖ ^ (2 : ℕ) := by
      rw [abs_mul]
      exact (mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)
    have hden : 0 < 4 * t ^ 2 := by positivity
    have hdiag : |(if i = j then 1 / (2 * t) else 0 : ℝ)| ≤ 1 / (2 * t) := by
      by_cases hij : i = j
      · rw [if_pos hij, abs_of_pos (by positivity : 0 < (1 : ℝ) / (2 * t))]
      · rw [if_neg hij, abs_zero]
        positivity
    have hcoef :
        |(x - y : E3) i * (x - y : E3) j / (4 * t ^ 2) -
          (if i = j then 1 / (2 * t) else 0)| ≤
          ‖x - y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t) := by
      calc
        |(x - y : E3) i * (x - y : E3) j / (4 * t ^ 2) -
            (if i = j then 1 / (2 * t) else 0)| ≤
            |(x - y : E3) i * (x - y : E3) j / (4 * t ^ 2)| +
              |(if i = j then 1 / (2 * t) else 0)| := by
          simpa [abs_neg] using
            (abs_sub_le ((x - y : E3) i * (x - y : E3) j / (4 * t ^ 2))
              (0 : ℝ) (if i = j then 1 / (2 * t) else 0))
        _ = |(x - y : E3) i * (x - y : E3) j| / (4 * t ^ 2) +
              |(if i = j then 1 / (2 * t) else 0)| := by
          rw [abs_div, abs_of_pos hden]
        _ ≤ ‖x - y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t) := by
          exact add_le_add (div_le_div_of_nonneg_right hprod hden.le) hdiag
    have ha : 0 ≤ ‖x - y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t) := by
      positivity
    have haD := hpoly_hess x y hxy
    rw [euclideanHeatKernel_three_hessian_formula ht (x-y) i j,
      abs_mul, abs_of_nonneg hKpos]
    exact (mul_le_mul_of_nonneg_right hcoef hKpos).trans
      (hdom x y _ ha haD hxy)
  exact ⟨hkernel, hgrad, hhess⟩
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
