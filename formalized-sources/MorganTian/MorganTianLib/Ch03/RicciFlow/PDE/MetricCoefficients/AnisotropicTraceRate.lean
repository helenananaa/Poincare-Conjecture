import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicFractionalMoment
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ProbabilityConvolutionTrace
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHolderOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** anisotropic trace rate. -/
theorem anisotropic_trace_rate 
    (B : E3 ≃L[ℝ] E3) (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E3 →ᵇ ℝ) (H : ℝ), 0 ≤ H →
      (∀ x y, |f x-f y| ≤ H*‖x-y‖^alpha) →
      ∀ t : ℝ, 0 < t → ∃ S : E3 →ᵇ ℝ,
        (∀ x, S x = ∫ y : E3, anisotropicHeatKernel B t y*f (x-y)) ∧
        ‖S-f‖ ≤ C*H*t^(alpha/2) ∧
        ∀ x y, |S x-S y| ≤ H*‖x-y‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C₀, hC₀, hmoment⟩ := anisotropic_fractional_moment alpha ha ha1
  let C : ℝ := C₀ * ‖B.toContinuousLinearMap‖ ^ alpha + 1
  have hCpos : 0 < C := by
    dsimp [C]
    have hrpow : 0 ≤ ‖B.toContinuousLinearMap‖ ^ alpha :=
      Real.rpow_nonneg (norm_nonneg _) _
    linarith [mul_nonneg hC₀.le hrpow]
  refine ⟨C, hCpos, ?_⟩
  intro f H hH hf t ht
  obtain ⟨hK, hMass, hKpos⟩ := anisotropic_heat_kernel_mass B t ht
  obtain ⟨S, hS, hSnorm, hSH⟩ :=
    anisotropic_holder_operator B t ht alpha H hH f hf
  have hmomentBt := hmoment B t ht
  have htrace := probability_convolution_trace_error
    (anisotropicHeatKernel B t) hK hKpos hMass alpha H hH
    hmomentBt.1 f hf
  have herror : ‖S - f‖ ≤ C * H * t ^ (alpha / 2) := by
    have htarget_nonneg : 0 ≤ C * H * t ^ (alpha / 2) := by
      apply mul_nonneg
      · exact mul_nonneg hCpos.le hH
      · exact Real.rpow_nonneg ht.le _
    apply (BoundedContinuousFunction.norm_le htarget_nonneg).2
    intro x
    rw [Real.norm_eq_abs]
    calc
      |(S - f) x| = |(∫ y : E3, anisotropicHeatKernel B t y * f (x - y)) - f x| := by
        change |S x - f x| = _
        rw [hS x]
      _ ≤ H * (∫ y : E3, anisotropicHeatKernel B t y * ‖y‖ ^ alpha) := htrace x
      _ ≤ H * (C₀ * ‖B.toContinuousLinearMap‖ ^ alpha * t ^ (alpha / 2)) := by
        exact mul_le_mul_of_nonneg_left hmomentBt.2 hH
      _ ≤ C * H * t ^ (alpha / 2) := by
        dsimp [C]
        have hpow : 0 ≤ t ^ (alpha / 2) := Real.rpow_nonneg ht.le _
        have hcoef : C₀ * ‖B.toContinuousLinearMap‖ ^ alpha ≤
            C₀ * ‖B.toContinuousLinearMap‖ ^ alpha + 1 := by linarith
        calc
          H * (C₀ * ‖B.toContinuousLinearMap‖ ^ alpha * t ^ (alpha / 2)) =
              (C₀ * ‖B.toContinuousLinearMap‖ ^ alpha) * H * t ^ (alpha / 2) := by ring
          _ ≤ (C₀ * ‖B.toContinuousLinearMap‖ ^ alpha + 1) * H * t ^ (alpha / 2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcoef hH) hpow
          _ = C * H * t ^ (alpha / 2) := by rfl
  exact ⟨S, hS, herror, hSH⟩
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
