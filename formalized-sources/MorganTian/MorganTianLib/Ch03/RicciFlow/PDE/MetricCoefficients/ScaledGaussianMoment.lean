import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
def scaledGaussianMoment (alpha beta t : ℝ) (y : E3) : ℝ :=
  MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2*t) y *
    ‖y‖^beta / t^((beta-alpha+3)/2)

/-- **Math.** scaled gaussian moment. -/
theorem scaled_gaussian_moment 
    (alpha beta : ℝ) (hb : 0 ≤ beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (scaledGaussianMoment alpha beta t) volume ∧
      (∫ y : E3, scaledGaussianMoment alpha beta t y) ≤ C*t^(alpha/2-3/2) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨Cβ, hCβ, hmoment⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_nonnegative_moment beta hb
  let q : ℝ := (beta - alpha + 3) / 2
  let C : ℝ := Cβ * 2 ^ (beta / 2)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t ht
  have h2t : 0 < 2 * t := by positivity
  have hbase := hmoment (2 * t) h2t
  have hden : 0 < t ^ q := Real.rpow_pos_of_pos ht q
  have hscale : ∀ y : E3,
      scaledGaussianMoment alpha beta t y =
        (1 / t ^ q) *
          (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2 * t) y * ‖y‖ ^ beta) := by
    intro y
    simp only [scaledGaussianMoment]
    dsimp [q]
    ring
  refine ⟨?_, ?_⟩
  · have heq : scaledGaussianMoment alpha beta t = fun y : E3 =>
        (1 / t ^ q) *
          (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2 * t) y * ‖y‖ ^ beta) := by
      funext y
      exact hscale y
    rw [heq]
    exact hbase.1.const_mul (1 / t ^ q)
  · have hratio : (2 * t) ^ (beta / 2) / t ^ q =
        2 ^ (beta / 2) * t ^ (alpha / 2 - 3 / 2) := by
      calc
        (2 * t) ^ (beta / 2) / t ^ q =
            2 ^ (beta / 2) * (t ^ (beta / 2) / t ^ q) := by
              rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) ht.le]
              ring
        _ = 2 ^ (beta / 2) * t ^ (beta / 2 - q) := by
              rw [Real.rpow_sub ht (beta / 2) q]
        _ = 2 ^ (beta / 2) * t ^ (alpha / 2 - 3 / 2) := by
              congr 1
              dsimp [q]
              ring
    have hcoeff : (1 / t ^ q) * (Cβ * (2 * t) ^ (beta / 2)) =
        C * t ^ (alpha / 2 - 3 / 2) := by
      calc
        (1 / t ^ q) * (Cβ * (2 * t) ^ (beta / 2)) =
            Cβ * ((2 * t) ^ (beta / 2) / t ^ q) := by ring
        _ = C * t ^ (alpha / 2 - 3 / 2) := by
            rw [hratio]
            dsimp [C]
            ring
    calc
      (∫ y : E3, scaledGaussianMoment alpha beta t y) =
          (1 / t ^ q) *
            (∫ y : E3,
              MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2 * t) y * ‖y‖ ^ beta) := by
          have heq : scaledGaussianMoment alpha beta t = fun y : E3 =>
              (1 / t ^ q) *
                (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2 * t) y * ‖y‖ ^ beta) := by
            funext y
            exact hscale y
          rw [heq, integral_const_mul]
      _ ≤ (1 / t ^ q) * (Cβ * (2 * t) ^ (beta / 2)) :=
          mul_le_mul_of_nonneg_left hbase.2 (by positivity)
      _ = C * t ^ (alpha / 2 - 3 / 2) := hcoeff
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
