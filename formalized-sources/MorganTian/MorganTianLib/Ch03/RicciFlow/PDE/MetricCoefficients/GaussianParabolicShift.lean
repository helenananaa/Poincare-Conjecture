import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** gaussian parabolic shift. -/
theorem gaussian_parabolic_shift 
    (t : ℝ) (ht : 0 < t) (y h : E3) (hh : ‖h‖ ≤ Real.sqrt t) :
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (y+h) ≤
      (8*Real.exp 1)*MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2*t) y :=
/- SWARM_PROOF_BEGIN -/
by
  rw [MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_norm_form,
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_norm_form]
  let A : ℝ := Real.sqrt (4 * Real.pi * t)
  let B : ℝ := Real.sqrt (4 * Real.pi * (2 * t))
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hroot : B = A * Real.sqrt 2 := by
    dsimp [A, B]
    calc
      Real.sqrt (4 * Real.pi * (2 * t)) = Real.sqrt ((4 * Real.pi * t) * 2) := by
        congr 1 <;> ring
      _ = Real.sqrt (4 * Real.pi * t) * Real.sqrt 2 := by
        rw [Real.sqrt_mul (by positivity)]
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    have hs := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hdenom : B ≤ 2 * A := by
    calc
      B = A * Real.sqrt 2 := hroot
      _ ≤ A * 2 := mul_le_mul_of_nonneg_left hsqrt2 hA.le
      _ = 2 * A := by ring
  have hInv2 : (2 * A)⁻¹ ≤ B⁻¹ :=
    (inv_le_inv₀ (by positivity : 0 < 2 * A) hB).2 hdenom
  have hInvEq : (2 * A)⁻¹ = (1 / 2 : ℝ) * A⁻¹ := by
    field_simp [ne_of_gt hA]
  have hinv : A⁻¹ ≤ 2 * B⁻¹ := by
    rw [hInvEq] at hInv2
    nlinarith
  have hnorm : A⁻¹ ^ (3 : ℕ) ≤ 8 * B⁻¹ ^ (3 : ℕ) := by
    calc
      A⁻¹ ^ (3 : ℕ) ≤ (2 * B⁻¹) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hinv _
      _ = 8 * B⁻¹ ^ (3 : ℕ) := by norm_num [mul_pow]
  have hy : ‖y‖ ≤ ‖y + h‖ + ‖h‖ := by
    calc
      ‖y‖ = ‖(y + h) - h‖ := by congr 1 <;> abel
      _ ≤ ‖y + h‖ + ‖h‖ := norm_sub_le _ _
  have hquad : ‖y‖ ^ 2 ≤ 2 * ‖y + h‖ ^ 2 + 2 * ‖h‖ ^ 2 := by
    have hp : 0 ≤ (‖y + h‖ + ‖h‖ - ‖y‖) *
        (‖y + h‖ + ‖h‖ + ‖y‖) :=
      mul_nonneg (by linarith [hy]) (by positivity)
    nlinarith [hp, sq_nonneg (‖y + h‖ - ‖h‖)]
  have hshift : ‖y‖ ^ 2 / 2 - ‖h‖ ^ 2 ≤ ‖y + h‖ ^ 2 := by
    nlinarith [hquad]
  have hhsq : ‖h‖ ^ 2 ≤ t := by
    calc
      ‖h‖ ^ 2 ≤ (Real.sqrt t) ^ 2 := by
        have hp : 0 ≤ (Real.sqrt t - ‖h‖) * (Real.sqrt t + ‖h‖) :=
          mul_nonneg (by linarith [hh]) (by positivity)
        nlinarith [hp]
      _ = t := Real.sq_sqrt ht.le
  have harg : -‖y + h‖ ^ 2 / (4 * t) ≤
      (1 / 4 : ℝ) - ‖y‖ ^ 2 / (4 * (2 * t)) := by
    have ht' : 0 < 8 * t := by positivity
    field_simp
    nlinarith [hshift, hhsq]
  have hexp : Real.exp (-‖y + h‖ ^ 2 / (4 * t)) ≤
      Real.exp (1 / 4) * Real.exp (-‖y‖ ^ 2 / (4 * (2 * t))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    convert harg using 1 <;> ring
  have hexp' : Real.exp (1 / 4 : ℝ) ≤ Real.exp 1 := by
    exact Real.exp_le_exp.mpr (by norm_num)
  have hcoef : A⁻¹ ^ (3 : ℕ) * Real.exp (1 / 4) ≤
      (8 * B⁻¹ ^ (3 : ℕ)) * Real.exp 1 :=
    mul_le_mul hnorm hexp' (by positivity) (by positivity)
  change A⁻¹ ^ (3 : ℕ) * Real.exp (-‖y + h‖ ^ 2 / (4 * t)) ≤
    (8 * Real.exp 1) * (B⁻¹ ^ (3 : ℕ) *
      Real.exp (-‖y‖ ^ 2 / (4 * (2 * t))))
  calc
    A⁻¹ ^ (3 : ℕ) * Real.exp (-‖y + h‖ ^ 2 / (4 * t)) ≤
        A⁻¹ ^ (3 : ℕ) *
          (Real.exp (1 / 4) * Real.exp (-‖y‖ ^ 2 / (4 * (2 * t)))) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (A⁻¹ ^ (3 : ℕ) * Real.exp (1 / 4)) *
        Real.exp (-‖y‖ ^ 2 / (4 * (2 * t))) := by ring
    _ ≤ ((8 * B⁻¹ ^ (3 : ℕ)) * Real.exp 1) *
        Real.exp (-‖y‖ ^ 2 / (4 * (2 * t))) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = (8 * Real.exp 1) * (B⁻¹ ^ (3 : ℕ) *
        Real.exp (-‖y‖ ^ 2 / (4 * (2 * t)))) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
