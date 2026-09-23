import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicTraceRate
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.HolderScaleInterpolation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** anisotropic lower holder trace. -/
theorem anisotropic_lower_holder_trace 
    (B : E3 ≃L[ℝ] E3) (alpha beta : ℝ) (hb : 0 < beta)
    (hba : beta < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E3 →ᵇ ℝ) (H : ℝ), 0 ≤ H →
      (∀ x y, |f x-f y| ≤ H*‖x-y‖^alpha) →
      ∀ t : ℝ, 0 < t → ∃ S : E3 →ᵇ ℝ,
        (∀ x, S x = ∫ y : E3, anisotropicHeatKernel B t y*f (x-y)) ∧
        ‖S-f‖ ≤ C*H*t^(alpha/2) ∧ ∀ x y,
          |(S x-f x)-(S y-f y)| ≤ C*H*t^((alpha-beta)/2)*‖x-y‖^beta :=
/- SWARM_PROOF_BEGIN -/
by
  have ha : 0 < alpha := lt_trans hb hba
  obtain ⟨C₀, hC₀, htrace⟩ := anisotropic_trace_rate B alpha ha ha1
  let C : ℝ := 2 * (1 + C₀)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro f H hH hf t ht
  obtain ⟨S, hS, herror, hSH⟩ := htrace f H hH hf t ht
  let delta : ℝ := C₀ * H * t ^ (alpha / 2)
  let r : ℝ := t ^ ((1 : ℝ) / 2)
  let g : E3 → ℝ := fun x => (S - f) x
  have hC0le : C₀ ≤ C := by
    dsimp [C]
    linarith [hC₀]
  have hpowalpha : 0 ≤ t ^ (alpha / 2) := Real.rpow_nonneg ht.le _
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    exact mul_nonneg (mul_nonneg hC₀.le hH) hpowalpha
  have hr : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos ht _
  have hbound : ∀ x, ‖g x‖ ≤ delta := by
    intro x
    have hnorm : ‖S - f‖ ≤ delta := by
      simpa [delta] using herror
    exact (BoundedContinuousFunction.norm_le hdelta).1 hnorm x
  have hholder : ∀ x y, ‖g x - g y‖ ≤ (2 * H) * ‖x - y‖ ^ alpha := by
    intro x y
    have hsplit :
        ‖(S x - f x) - (S y - f y)‖ ≤ ‖S x - S y‖ + ‖f x - f y‖ := by
      calc
        ‖(S x - f x) - (S y - f y)‖ = ‖(S x - S y) - (f x - f y)‖ := by
          congr 1; ring
        _ ≤ ‖S x - S y‖ + ‖f x - f y‖ := norm_sub_le _ _
    calc
      ‖g x - g y‖ = ‖(S x - f x) - (S y - f y)‖ := by rfl
      _ ≤ ‖S x - S y‖ + ‖f x - f y‖ := hsplit
      _ ≤ H * ‖x - y‖ ^ alpha + H * ‖x - y‖ ^ alpha := by
        exact add_le_add
          (by simpa [Real.norm_eq_abs] using hSH x y)
          (by simpa [Real.norm_eq_abs] using hf x y)
      _ = (2 * H) * ‖x - y‖ ^ alpha := by ring
  have hrpow : t ^ ((alpha - beta) / 2) = r ^ (alpha - beta) := by
    dsimp [r]
    calc
      t ^ ((alpha - beta) / 2) = t ^ ((1 / 2) * (alpha - beta)) := by
        congr 1; ring
      _ = (t ^ (1 / 2)) ^ (alpha - beta) := Real.rpow_mul ht.le _ _
  have hden : r ^ beta = t ^ (beta / 2) := by
    dsimp [r]
    calc
      (t ^ (1 / 2)) ^ beta = t ^ ((1 / 2) * beta) := (Real.rpow_mul ht.le _ _).symm
      _ = t ^ (beta / 2) := by congr 1; ring
  have hratio : t ^ (alpha / 2) / r ^ beta = t ^ ((alpha - beta) / 2) := by
    rw [hden]
    calc
      t ^ (alpha / 2) / t ^ (beta / 2) = t ^ (alpha / 2 - beta / 2) :=
        (Real.rpow_sub ht _ _).symm
      _ = t ^ ((alpha - beta) / 2) := by congr 1; ring
  have hdeltaRatio : delta / r ^ beta = C₀ * H * t ^ ((alpha - beta) / 2) := by
    calc
      delta / r ^ beta = (C₀ * H * t ^ (alpha / 2)) / r ^ beta := by
        simp [delta]
      _ = C₀ * H * (t ^ (alpha / 2) / r ^ beta) := by ring
      _ = C₀ * H * t ^ ((alpha - beta) / 2) := by rw [hratio]
  have hcoeff :
      2 * H * r ^ (alpha - beta) + 2 * delta / r ^ beta =
        C * H * t ^ ((alpha - beta) / 2) := by
    rw [← hrpow]
    have htwodelta : 2 * delta / r ^ beta = 2 * (delta / r ^ beta) := by ring
    rw [htwodelta, hdeltaRatio]
    dsimp [C]
    ring
  have hinterp := holder_scale_interpolation g alpha beta (2 * H) delta r
    hb hba (mul_nonneg (by norm_num) hH) hdelta hr hbound hholder
  refine ⟨S, hS, ?_, ?_⟩
  · exact le_trans herror (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC0le hH) hpowalpha)
  · intro x y
    calc
      |(S x - f x) - (S y - f y)| ≤
          (2 * H * r ^ (alpha - beta) + 2 * delta / r ^ beta) *
            ‖x - y‖ ^ beta := by
        simpa [g, Real.norm_eq_abs] using hinterp x y
      _ = C * H * t ^ ((alpha - beta) / 2) * ‖x - y‖ ^ beta := by
        rw [hcoeff]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
