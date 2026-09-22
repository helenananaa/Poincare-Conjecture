import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TimeDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatFirstFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatGradientFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatHessianContinuous
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction RealInnerProductSpace
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- A single local majorant for actual spatial derivatives across a compact positive-time interval. -/
theorem compact_time_spatial_derivative_dominator (a b R : ℝ)
    (ha : 0<a) (hab : a≤b) (hR : 0≤R) :
    ∃ g : E3 → ℝ, Integrable g volume ∧ (∀ y, 0≤g y) ∧
      ∀ t∈Icc a b, ∀ x y : E3, ‖x‖≤R →
        |euclideanHeatKernel 3 t (x-y)| ≤ g y ∧
        (∀ i : Fin 3, |fderiv ℝ (euclideanHeatKernel 3 t) (x-y) (EuclideanSpace.single i 1)| ≤ g y) ∧
        (∀ i j : Fin 3, |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)| ≤ g y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨g₀, hg₀, hg₀_nonneg, hdom⟩ :=
    euclideanHeatKernel_time_derivative_dominator a b R ha hab hR
  let M : ℝ := 3 + 3 / (2 * a) + 2 / a
  let g : E3 → ℝ := fun y => M * g₀ y
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hg : Integrable g volume := by
    dsimp [g]
    exact hg₀.const_mul M
  have hg_nonneg : ∀ y, 0 ≤ g y := by
    intro y
    dsimp [g]
    exact mul_nonneg hM (hg₀_nonneg y)
  refine ⟨g, hg, hg_nonneg, ?_⟩
  intro t ht x y hxy
  have hta : 0 < t := lt_of_lt_of_le ha ht.1
  have hK : 0 ≤ euclideanHeatKernel 3 t (x - y) :=
    (euclideanHeatKernel_pos 3 hta (x - y)).le
  have hbase := hdom t x y ht hxy
  have hKdom : |euclideanHeatKernel 3 t (x-y)| ≤ g₀ y := hbase.1
  have htdom : |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| ≤ g₀ y :=
    hbase.2
  have hKdom' : euclideanHeatKernel 3 t (x-y) ≤ g₀ y := by
    simpa [abs_of_nonneg hK] using hKdom
  have htd : deriv (fun s => euclideanHeatKernel 3 s (x-y)) t =
      (‖x-y‖ ^ 2 / (4*t^2) - 3/(2*t)) *
        euclideanHeatKernel 3 t (x-y) :=
    (euclideanHeatKernel_three_time_formula hta (x-y)).deriv
  have hqK :
      ‖x-y‖ ^ 2 / (4*t^2) * euclideanHeatKernel 3 t (x-y) ≤
        |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
          (3/(2*a)) * euclideanHeatKernel 3 t (x-y)
      := by
    have hca : 3/(2*t) ≤ 3/(2*a) := by
      calc
        3/(2*t) = (3/2) * (1/t) := by ring
        _ ≤ (3/2) * (1/a) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le ha ht.1)
            (by norm_num)
        _ = 3/(2*a) := by ring
    have hq' : ‖x-y‖ ^ 2 / (4*t^2) ≤
        |‖x-y‖ ^ 2 / (4*t^2) - 3/(2*t)| + 3/(2*t) := by
      have := le_abs_self (‖x-y‖ ^ 2 / (4*t^2) - 3/(2*t))
      linarith
    calc
      ‖x-y‖ ^ 2 / (4*t^2) * euclideanHeatKernel 3 t (x-y) ≤
          (|‖x-y‖ ^ 2 / (4*t^2) - 3/(2*t)| + 3/(2*t)) *
            euclideanHeatKernel 3 t (x-y) :=
        mul_le_mul_of_nonneg_right hq' hK
      _ = |(‖x-y‖ ^ 2 / (4*t^2) - 3/(2*t)) *
            euclideanHeatKernel 3 t (x-y)| +
          (3/(2*t)) * euclideanHeatKernel 3 t (x-y) := by
        rw [abs_mul, abs_of_nonneg hK]
        ring
      _ = |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
          (3/(2*t)) * euclideanHeatKernel 3 t (x-y) := by rw [htd]
      _ ≤ |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
          (3/(2*a)) * euclideanHeatKernel 3 t (x-y) := by
        simpa [add_comm] using
          (add_le_add_left (mul_le_mul_of_nonneg_right hca hK)
            |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t|)
  have hgrad (i : Fin 3) :
      |fderiv ℝ (euclideanHeatKernel 3 t) (x-y)
          (EuclideanSpace.single i 1)| ≤ g y := by
    let r : ℝ := |(x-y : E3) i| / (2*t)
    have hi : |(x-y : E3) i| ≤ ‖x-y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (x-y) i)
    have hr : 0 ≤ r := by
      dsimp [r]
      positivity
    have hcoord_sq : |(x-y : E3) i| ^ 2 ≤ ‖x-y‖ ^ 2 := by
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hi
    have hr_sq : r ^ 2 ≤ ‖x-y‖ ^ 2 / (4*t^2) := by
      dsimp [r]
      calc
        (|(x-y : E3) i| / (2*t)) ^ 2 =
            |(x-y : E3) i| ^ 2 / (4*t^2) := by
              field_simp [ne_of_gt hta]
              ring
        _ ≤ ‖x-y‖ ^ 2 / (4*t^2) :=
          div_le_div_of_nonneg_right hcoord_sq (by positivity)
    have hrr : r ≤ r ^ 2 + 1 := by
      nlinarith [sq_nonneg (r - (1/2 : ℝ))]
    have hgrad_raw :
        r * euclideanHeatKernel 3 t (x-y) ≤
          |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
            (3/(2*a)) * euclideanHeatKernel 3 t (x-y) +
              euclideanHeatKernel 3 t (x-y) := by
      have hrr' : r ≤ ‖x-y‖ ^ 2 / (4*t^2) + 1 :=
        hrr.trans (by simpa [add_comm] using add_le_add_right hr_sq 1)
      have hmul := mul_le_mul_of_nonneg_right hrr' hK
      linarith
    have hgrad_majorant :
        r * euclideanHeatKernel 3 t (x-y) ≤ M * g₀ y := by
      have h₁ :
          |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| ≤ g₀ y := htdom
      have h₂ :
          (3/(2*a)) * euclideanHeatKernel 3 t (x-y) ≤
            (3/(2*a)) * g₀ y :=
        mul_le_mul_of_nonneg_left hKdom' (by positivity)
      have h₃ :
          euclideanHeatKernel 3 t (x-y) ≤ g₀ y := hKdom'
      have hsum :
          |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
              (3/(2*a)) * euclideanHeatKernel 3 t (x-y) +
                euclideanHeatKernel 3 t (x-y) ≤
            g₀ y + (3/(2*a)) * g₀ y + g₀ y := by
        exact add_le_add (add_le_add h₁ h₂) h₃
      calc
        r * euclideanHeatKernel 3 t (x-y) ≤
            |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
              (3/(2*a)) * euclideanHeatKernel 3 t (x-y) +
                euclideanHeatKernel 3 t (x-y) := hgrad_raw
        _ ≤ g₀ y + (3/(2*a)) * g₀ y + g₀ y := hsum
        _ ≤ M * g₀ y := by
          dsimp [M]
          nlinarith [mul_nonneg (show 0 ≤ 2/a by positivity) (hg₀_nonneg y)]
    rw [euclideanHeatKernel_three_gradient_formula hta (x-y) i,
      abs_mul, abs_neg, abs_div,
      abs_of_pos (show 0 < 2*t by positivity), abs_of_nonneg hK]
    exact hgrad_majorant
  have hhess (i j : Fin 3) :
      |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)| ≤ g y := by
    have hi : |(x-y : E3) i| ≤ ‖x-y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (x-y) i)
    have hj : |(x-y : E3) j| ≤ ‖x-y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (x-y) j)
    have hprod : |(x-y : E3) i * (x-y : E3) j| ≤ ‖x-y‖ ^ (2 : ℕ) := by
      rw [abs_mul]
      exact (mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)
    have hden : 0 < 4*t^2 := by positivity
    have hdiag : |(if i=j then 1/(2*t) else 0 : ℝ)| ≤ 1/(2*t) := by
      by_cases hij : i = j
      · rw [if_pos hij, abs_of_pos (by positivity : 0 < (1:ℝ)/(2*t))]
      · rw [if_neg hij, abs_zero]
        positivity
    have hcoef :
        |(x-y : E3) i * (x-y : E3) j / (4*t^2) -
          (if i=j then 1/(2*t) else 0)| ≤
          ‖x-y‖ ^ (2 : ℕ) / (4*t^2) + 1/(2*t) := by
      calc
        |(x-y : E3) i * (x-y : E3) j / (4*t^2) -
            (if i=j then 1/(2*t) else 0)| ≤
            |(x-y : E3) i * (x-y : E3) j / (4*t^2)| +
              |(if i=j then 1/(2*t) else 0)| := by
          simpa [abs_neg] using
            (abs_sub_le ((x-y : E3) i * (x-y : E3) j / (4*t^2))
              (0 : ℝ) (if i=j then 1/(2*t) else 0))
        _ = |(x-y : E3) i * (x-y : E3) j| / (4*t^2) +
              |(if i=j then 1/(2*t) else 0)| := by
          rw [abs_div, abs_of_pos hden]
        _ ≤ ‖x-y‖ ^ (2 : ℕ) / (4*t^2) + 1/(2*t) := by
          exact add_le_add (div_le_div_of_nonneg_right hprod hden.le) hdiag
    have hqdiag :
        (‖x-y‖ ^ 2 / (4*t^2) + 1/(2*t)) *
            euclideanHeatKernel 3 t (x-y) ≤
          |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
            (2/a) * euclideanHeatKernel 3 t (x-y) := by
      have hdiag_time : 1/(2*t) ≤ 1/(2*a) := by
        calc
          1/(2*t) = (1/2) * (1/t) := by ring
          _ ≤ (1/2) * (1/a) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le ha ht.1)
              (by norm_num)
          _ = 1/(2*a) := by ring
      have hdiag' := mul_le_mul_of_nonneg_right hdiag_time hK
      calc
        (‖x-y‖ ^ 2 / (4*t^2) + 1/(2*t)) *
            euclideanHeatKernel 3 t (x-y) =
          ‖x-y‖ ^ 2 / (4*t^2) * euclideanHeatKernel 3 t (x-y) +
            1/(2*t) * euclideanHeatKernel 3 t (x-y) := by ring
        _ ≤ (|deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
              (3/(2*a)) * euclideanHeatKernel 3 t (x-y)) +
            1/(2*t) * euclideanHeatKernel 3 t (x-y) :=
          add_le_add hqK (le_refl _)
        _ ≤ (|deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
              (3/(2*a)) * euclideanHeatKernel 3 t (x-y)) +
            1/(2*a) * euclideanHeatKernel 3 t (x-y) :=
          by
            simpa [add_comm] using
              (add_le_add_left hdiag'
                (|deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
                  (3/(2*a)) * euclideanHeatKernel 3 t (x-y)))
        _ = |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
              (2/a) * euclideanHeatKernel 3 t (x-y) := by ring
    have hhess_majorant :
        |(‖x-y‖ ^ 2 / (4*t^2) + 1/(2*t)) *
            euclideanHeatKernel 3 t (x-y)| ≤ M * g₀ y := by
      rw [abs_of_nonneg (by positivity)]
      have h₁ :
          |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| ≤ g₀ y := htdom
      have h₂ :
          (2/a) * euclideanHeatKernel 3 t (x-y) ≤ (2/a) * g₀ y :=
        mul_le_mul_of_nonneg_left hKdom' (by positivity)
      have hsum :
          |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
              (2/a) * euclideanHeatKernel 3 t (x-y) ≤
            g₀ y + (2/a) * g₀ y := add_le_add h₁ h₂
      calc
        (‖x-y‖ ^ 2 / (4*t^2) + 1/(2*t)) *
            euclideanHeatKernel 3 t (x-y) ≤
            |deriv (fun s => euclideanHeatKernel 3 s (x-y)) t| +
              (2/a) * euclideanHeatKernel 3 t (x-y) := hqdiag
        _ ≤ g₀ y + (2/a) * g₀ y := hsum
        _ ≤ M * g₀ y := by
          dsimp [M]
          nlinarith [mul_nonneg (show 0 ≤ 2 + 3/(2*a) by positivity)
            (hg₀_nonneg y)]
    rw [euclideanHeatKernel_three_hessian_formula hta (x-y) i j,
      abs_mul, abs_of_nonneg hK]
    have hqdiag_nonneg :
        0 ≤ (‖x-y‖ ^ 2 / (4*t^2) + 1/(2*t)) *
            euclideanHeatKernel 3 t (x-y) := by positivity
    calc
      |(x-y : E3) i * (x-y : E3) j / (4*t^2) -
          (if i=j then 1/(2*t) else 0)| *
          euclideanHeatKernel 3 t (x-y) ≤
        (‖x-y‖ ^ 2 / (4*t^2) + 1/(2*t)) *
          euclideanHeatKernel 3 t (x-y) :=
        mul_le_mul_of_nonneg_right hcoef hK
      _ = |(‖x-y‖ ^ 2 / (4*t^2) + 1/(2*t)) *
          euclideanHeatKernel 3 t (x-y)| :=
        (abs_of_nonneg hqdiag_nonneg).symm
      _ ≤ M * g₀ y := hhess_majorant
      _ = g y := by rfl
  have hM1 : 1 ≤ M := by
    dsimp [M]
    nlinarith [show 0 ≤ 3/(2*a) by positivity, show 0 ≤ 2/a by positivity]
  have hkernel : |euclideanHeatKernel 3 t (x-y)| ≤ g y := by
    rw [abs_of_nonneg hK]
    calc
      euclideanHeatKernel 3 t (x-y) ≤ g₀ y := hKdom'
      _ ≤ M * g₀ y := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hM1 (hg₀_nonneg y))
      _ = g y := by rfl
  exact ⟨hkernel, hgrad, hhess⟩
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
