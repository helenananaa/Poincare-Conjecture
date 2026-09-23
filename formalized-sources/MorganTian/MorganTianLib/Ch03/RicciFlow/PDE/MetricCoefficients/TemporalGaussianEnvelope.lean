import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
def temporalGaussianEnvelope (alpha t : ℝ) (y : E3) : ℝ :=
  64*MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2*t) y *
    (‖y‖^alpha/t^2+‖y‖^(alpha+2)/t^3+‖y‖^(alpha+4)/t^4)

/-- **Math.** temporal gaussian envelope integral. -/
theorem temporal_gaussian_envelope_integral 
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (temporalGaussianEnvelope alpha t) volume ∧
      (∀ y : E3, 0 ≤ temporalGaussianEnvelope alpha t y) ∧
      (∫ y : E3, temporalGaussianEnvelope alpha t y) ≤ C*t^(alpha/2-2) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C₀, hC₀, hm₀⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_nonnegative_moment
      alpha ha.le
  obtain ⟨C₁, hC₁, hm₁⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_nonnegative_moment
      (alpha + 2) (by linarith)
  obtain ⟨C₂, hC₂, hm₂⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_nonnegative_moment
      (alpha + 4) (by linarith)
  let C : ℝ := 64 *
    (C₀ * 2 ^ (alpha / 2) +
      C₁ * 2 ^ ((alpha + 2) / 2) +
      C₂ * 2 ^ ((alpha + 4) / 2))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t ht
  have h2t : 0 < 2 * t := by positivity
  have hb₀ := hm₀ (2 * t) h2t
  have hb₁ := hm₁ (2 * t) h2t
  have hb₂ := hm₂ (2 * t) h2t
  let K : E3 → ℝ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2 * t)
  let f₀ : E3 → ℝ := fun y => K y * ‖y‖ ^ alpha / t ^ 2
  let f₁ : E3 → ℝ := fun y => K y * ‖y‖ ^ (alpha + 2) / t ^ 3
  let f₂ : E3 → ℝ := fun y => K y * ‖y‖ ^ (alpha + 4) / t ^ 4
  have hi₀ : Integrable f₀ volume := by
    have h := hb₀.1.mul_const ((t ^ 2)⁻¹)
    convert h using 1
    ext y
    simp [f₀, K, div_eq_mul_inv]
  have hi₁ : Integrable f₁ volume := by
    have h := hb₁.1.mul_const ((t ^ 3)⁻¹)
    convert h using 1
    ext y
    simp [f₁, K, div_eq_mul_inv]
  have hi₂ : Integrable f₂ volume := by
    have h := hb₂.1.mul_const ((t ^ 4)⁻¹)
    convert h using 1
    ext y
    simp [f₂, K, div_eq_mul_inv]
  have heq : temporalGaussianEnvelope alpha t =
      fun y : E3 => 64 * (f₀ y + (f₁ y + f₂ y)) := by
    funext y
    simp only [temporalGaussianEnvelope, f₀, f₁, f₂, K]
    ring
  have hInt : Integrable (temporalGaussianEnvelope alpha t) volume := by
    rw [heq]
    exact (hi₀.add (hi₁.add hi₂)).const_mul 64
  have hnonneg : ∀ y : E3, 0 ≤ temporalGaussianEnvelope alpha t y := by
    intro y
    rw [heq]
    have hK : 0 ≤ K y := by
      dsimp [K]
      exact (MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos 3 h2t y).le
    have hn : 0 ≤ ‖y‖ := norm_nonneg y
    have ht2 : 0 < t ^ 2 := by positivity
    have ht3 : 0 < t ^ 3 := by positivity
    have ht4 : 0 < t ^ 4 := by positivity
    dsimp [f₀, f₁, f₂]
    positivity
  have hratio (b : ℝ) (n : ℕ) (hrel : b / 2 - (n : ℝ) = alpha / 2 - 2) :
      (2 * t) ^ (b / 2) / t ^ n =
        2 ^ (b / 2) * t ^ (alpha / 2 - 2) := by
    calc
      (2 * t) ^ (b / 2) / t ^ n =
          (2 * t) ^ (b / 2) / t ^ (n : ℝ) := by
            rw [← Real.rpow_natCast t n]
      _ = 2 ^ (b / 2) * (t ^ (b / 2) / t ^ (n : ℝ)) := by
            rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) ht.le]
            ring
      _ = 2 ^ (b / 2) * t ^ (b / 2 - (n : ℝ)) := by
            rw [Real.rpow_sub ht]
      _ = 2 ^ (b / 2) * t ^ (alpha / 2 - 2) := by rw [hrel]
  have hratio₀ : (2 * t) ^ (alpha / 2) / t ^ 2 =
      2 ^ (alpha / 2) * t ^ (alpha / 2 - 2) := by
    apply hratio alpha 2
    norm_num
  have hratio₁ : (2 * t) ^ ((alpha + 2) / 2) / t ^ 3 =
      2 ^ ((alpha + 2) / 2) * t ^ (alpha / 2 - 2) := by
    apply hratio (alpha + 2) 3
    ring
  have hratio₂ : (2 * t) ^ ((alpha + 4) / 2) / t ^ 4 =
      2 ^ ((alpha + 4) / 2) * t ^ (alpha / 2 - 2) := by
    apply hratio (alpha + 4) 4
    ring
  have hv₀ : (∫ y : E3, f₀ y) =
      (∫ y : E3, K y * ‖y‖ ^ alpha) / t ^ 2 := by
    have hfun : f₀ = fun y : E3 =>
        (K y * ‖y‖ ^ alpha) * (t ^ 2)⁻¹ := by
      funext y
      simp [f₀, div_eq_mul_inv]
    rw [hfun, integral_mul_const, div_eq_mul_inv]
  have hv₁ : (∫ y : E3, f₁ y) =
      (∫ y : E3, K y * ‖y‖ ^ (alpha + 2)) / t ^ 3 := by
    have hfun : f₁ = fun y : E3 =>
        (K y * ‖y‖ ^ (alpha + 2)) * (t ^ 3)⁻¹ := by
      funext y
      simp [f₁, div_eq_mul_inv]
    rw [hfun, integral_mul_const, div_eq_mul_inv]
  have hv₂ : (∫ y : E3, f₂ y) =
      (∫ y : E3, K y * ‖y‖ ^ (alpha + 4)) / t ^ 4 := by
    have hfun : f₂ = fun y : E3 =>
        (K y * ‖y‖ ^ (alpha + 4)) * (t ^ 4)⁻¹ := by
      funext y
      simp [f₂, div_eq_mul_inv]
    rw [hfun, integral_mul_const, div_eq_mul_inv]
  have hs₀ : (∫ y : E3, f₀ y) ≤
      (C₀ * 2 ^ (alpha / 2)) * t ^ (alpha / 2 - 2) := by
    rw [hv₀]
    have hmul := mul_le_mul_of_nonneg_right hb₀.2
      (by positivity : 0 ≤ (t ^ 2)⁻¹)
    calc
      (∫ y : E3, K y * ‖y‖ ^ alpha) * (t ^ 2)⁻¹ ≤
          (C₀ * (2 * t) ^ (alpha / 2)) * (t ^ 2)⁻¹ := hmul
      _ = C₀ * ((2 * t) ^ (alpha / 2) / t ^ 2) := by ring
      _ = (C₀ * 2 ^ (alpha / 2)) * t ^ (alpha / 2 - 2) := by
          rw [hratio₀]
          ring
  have hs₁ : (∫ y : E3, f₁ y) ≤
      (C₁ * 2 ^ ((alpha + 2) / 2)) * t ^ (alpha / 2 - 2) := by
    rw [hv₁]
    have hmul := mul_le_mul_of_nonneg_right hb₁.2
      (by positivity : 0 ≤ (t ^ 3)⁻¹)
    calc
      (∫ y : E3, K y * ‖y‖ ^ (alpha + 2)) * (t ^ 3)⁻¹ ≤
          (C₁ * (2 * t) ^ ((alpha + 2) / 2)) * (t ^ 3)⁻¹ := hmul
      _ = C₁ * ((2 * t) ^ ((alpha + 2) / 2) / t ^ 3) := by ring
      _ = (C₁ * 2 ^ ((alpha + 2) / 2)) * t ^ (alpha / 2 - 2) := by
          rw [hratio₁]
          ring
  have hs₂ : (∫ y : E3, f₂ y) ≤
      (C₂ * 2 ^ ((alpha + 4) / 2)) * t ^ (alpha / 2 - 2) := by
    rw [hv₂]
    have hmul := mul_le_mul_of_nonneg_right hb₂.2
      (by positivity : 0 ≤ (t ^ 4)⁻¹)
    calc
      (∫ y : E3, K y * ‖y‖ ^ (alpha + 4)) * (t ^ 4)⁻¹ ≤
          (C₂ * (2 * t) ^ ((alpha + 4) / 2)) * (t ^ 4)⁻¹ := hmul
      _ = C₂ * ((2 * t) ^ ((alpha + 4) / 2) / t ^ 4) := by ring
      _ = (C₂ * 2 ^ ((alpha + 4) / 2)) * t ^ (alpha / 2 - 2) := by
          rw [hratio₂]
          ring
  refine ⟨hInt, hnonneg, ?_⟩
  have hsumint : (∫ y : E3, f₀ y + (f₁ y + f₂ y)) =
      (∫ y : E3, f₀ y) +
        ((∫ y : E3, f₁ y) + ∫ y : E3, f₂ y) := by
    have h12 : (∫ y : E3, (f₁ + f₂) y) =
        (∫ y : E3, f₁ y) + ∫ y : E3, f₂ y := by
      simpa only [Pi.add_apply] using (integral_add hi₁ hi₂)
    calc
      (∫ y : E3, f₀ y + (f₁ y + f₂ y)) =
          (∫ y : E3, f₀ y) + ∫ y : E3, (f₁ + f₂) y :=
            integral_add hi₀ (hi₁.add hi₂)
      _ = (∫ y : E3, f₀ y) +
          ((∫ y : E3, f₁ y) + ∫ y : E3, f₂ y) := by rw [h12]
  have hint_eq : (∫ y : E3, temporalGaussianEnvelope alpha t y) =
      64 * ((∫ y : E3, f₀ y) +
        ((∫ y : E3, f₁ y) + ∫ y : E3, f₂ y)) := by
    calc
      (∫ y : E3, temporalGaussianEnvelope alpha t y) =
          64 * (∫ y : E3, f₀ y + (f₁ y + f₂ y)) := by
            rw [heq, integral_const_mul]
      _ = 64 * ((∫ y : E3, f₀ y) +
          ((∫ y : E3, f₁ y) + ∫ y : E3, f₂ y)) := by rw [hsumint]
  rw [hint_eq]
  have hsum : (∫ y : E3, f₀ y) +
      ((∫ y : E3, f₁ y) + ∫ y : E3, f₂ y) ≤
      (C₀ * 2 ^ (alpha / 2) +
        C₁ * 2 ^ ((alpha + 2) / 2) +
        C₂ * 2 ^ ((alpha + 4) / 2)) * t ^ (alpha / 2 - 2) := by
    have hp : 0 ≤ t ^ (alpha / 2 - 2) := Real.rpow_nonneg ht.le _
    linarith [hs₀, hs₁, hs₂]
  calc
    64 * ((∫ y : E3, f₀ y) +
        ((∫ y : E3, f₁ y) + ∫ y : E3, f₂ y)) ≤
        64 * ((C₀ * 2 ^ (alpha / 2) +
          C₁ * 2 ^ ((alpha + 2) / 2) +
          C₂ * 2 ^ ((alpha + 4) / 2)) * t ^ (alpha / 2 - 2)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = C * t ^ (alpha / 2 - 2) := by
      dsimp [C]
      ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
