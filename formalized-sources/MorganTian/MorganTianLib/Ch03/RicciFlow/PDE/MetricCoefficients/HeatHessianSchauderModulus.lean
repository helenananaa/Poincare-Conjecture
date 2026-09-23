import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.HeatHessianSmallShift
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** heat hessian schauder modulus. -/
theorem heat_hessian_schauder_modulus 
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E3 →ᵇ ℝ) (L : ℝ), 0 ≤ L →
      (∀ x z : E3, |f x-f z| ≤ L*‖x-z‖^alpha) → ∀ t : ℝ, 0 < t →
      ∀ (x z : E3) (i j : Fin 3),
      |(∫ y : E3, heatHessian3 t i j y*f (x-y))-(∫ y : E3, heatHessian3 t i j y*f (z-y))| ≤
        C*L*min (t^(alpha/2-1)) (‖x-z‖*t^(alpha/2-3/2)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C₁, hC₁, hconv⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_holder_hessian_convolution
      alpha ha ha1
  obtain ⟨C₂, hC₂, hsmall⟩ := heat_hessian_small_shift alpha ha ha1
  refine ⟨max (2 * C₁) C₂, lt_max_of_lt_left ?_, ?_⟩
  · exact mul_pos (by norm_num) hC₁
  · intro f L hL hholder t ht x z i j
    let p : ℝ := alpha / 2 - 1
    let q : ℝ := alpha / 2 - 3 / 2
    let d : ℝ := ‖x - z‖
    let A : ℝ := ∫ y : E3, heatHessian3 t i j y * f (x - y)
    let B : ℝ := ∫ y : E3, heatHessian3 t i j y * f (z - y)
    have hA : |A| ≤ C₁ * L * t ^ p := by
      simpa [A, p, heatHessian3] using
        (hconv f L hL hholder t ht i j x).2
    have hB : |B| ≤ C₁ * L * t ^ p := by
      simpa [B, p, heatHessian3] using
        (hconv f L hL hholder t ht i j z).2
    have hp : 0 ≤ t ^ p := Real.rpow_nonneg ht.le _
    have hq : 0 ≤ t ^ q := Real.rpow_nonneg ht.le _
    have hglobal : |A - B| ≤ max (2 * C₁) C₂ * L * t ^ p := by
      have hcoef : 2 * C₁ * L ≤ max (2 * C₁) C₂ * L :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hL
      calc
        |A - B| ≤ |A| + |B| := abs_sub _ _
        _ ≤ C₁ * L * t ^ p + C₁ * L * t ^ p := add_le_add hA hB
        _ = (2 * C₁ * L) * t ^ p := by ring
        _ ≤ (max (2 * C₁) C₂ * L) * t ^ p :=
          mul_le_mul_of_nonneg_right hcoef hp
        _ = max (2 * C₁) C₂ * L * t ^ p := by ring
    have hscale (hnear : d ≤ Real.sqrt t) : d * t ^ q ≤ t ^ p := by
      have hroot : Real.sqrt t * t ^ q = t ^ p := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
        congr 1 <;> dsimp [p, q] <;> ring
      calc
        d * t ^ q ≤ Real.sqrt t * t ^ q :=
          mul_le_mul_of_nonneg_right hnear hq
        _ = t ^ p := hroot
    have hscaleFar (hfar : Real.sqrt t ≤ d) : t ^ p ≤ d * t ^ q := by
      have hroot : Real.sqrt t * t ^ q = t ^ p := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
        congr 1 <;> dsimp [p, q] <;> ring
      calc
        t ^ p = Real.sqrt t * t ^ q := hroot.symm
        _ ≤ d * t ^ q := mul_le_mul_of_nonneg_right hfar hq
    by_cases hnear : d ≤ Real.sqrt t
    · have hsmallbound := hsmall f L hL hholder t ht x z hnear i j
      have hcoef : C₂ * L ≤ max (2 * C₁) C₂ * L :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hL
      have hbound : |A - B| ≤ max (2 * C₁) C₂ * L * (d * t ^ q) := by
        calc
          |A - B| ≤ C₂ * L * (d * t ^ q) := by
            simpa only [A, B, d, q, mul_assoc] using hsmallbound
          _ ≤ (max (2 * C₁) C₂ * L) * (d * t ^ q) :=
            mul_le_mul_of_nonneg_right hcoef (mul_nonneg (norm_nonneg _) hq)
          _ = max (2 * C₁) C₂ * L * (d * t ^ q) := by ring
      rw [min_eq_right (hscale hnear)]
      simpa [A, B, d, q] using hbound
    · have hfar : Real.sqrt t ≤ d := le_of_not_ge hnear
      rw [min_eq_left (hscaleFar hfar)]
      simpa [A, B, d, p] using hglobal
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
