import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHeatKernel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ProbabilityConvolutionHolder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "JBg" => J3 × (T3 × (Fin 3 → T3))
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** anisotropic holder operator. -/
theorem anisotropic_holder_operator (B : E3 ≃L[ℝ] E3) (t : ℝ) (ht : 0 < t)
    (alpha H : ℝ) (hH : 0 ≤ H) (f : E3 →ᵇ ℝ)
    (hf : ∀ x y : E3, |f x-f y| ≤ H*‖x-y‖^alpha) :
    ∃ S : E3 →ᵇ ℝ, (∀ x, S x = ∫ y : E3, anisotropicHeatKernel B t y*f (x-y)) ∧
      ‖S‖ ≤ ‖f‖ ∧ ∀ x y, |S x-S y| ≤ H*‖x-y‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  rcases anisotropic_heat_kernel_mass B t ht with ⟨hK, hMass, hKpos⟩
  have hconv := probability_convolution_holder (anisotropicHeatKernel B t)
    hK hKpos hMass f alpha H hH hf
  let g : E3 → ℝ := fun x => ∫ y : E3, anisotropicHeatKernel B t y * f (x - y)
  have hmajor : Integrable (fun y : E3 => anisotropicHeatKernel B t y * ‖f‖) volume :=
    hK.mul_const ‖f‖
  have hbound (x y : E3) :
      ‖anisotropicHeatKernel B t y * f (x - y)‖ ≤
        anisotropicHeatKernel B t y * ‖f‖ := by
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (hKpos y)]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (hKpos y)
  have hfy (y : E3) : Continuous (fun x : E3 => f (x - y)) :=
    f.continuous.comp (continuous_id.sub continuous_const)
  have hgcontAt (x₀ : E3) : ContinuousAt g x₀ := by
    change Tendsto (fun x => ∫ y : E3,
      anisotropicHeatKernel B t y * f (x - y)) (𝓝 x₀)
      (𝓝 (∫ y : E3, anisotropicHeatKernel B t y * f (x₀ - y)))
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun y : E3 => anisotropicHeatKernel B t y * ‖f‖)
    · filter_upwards [] with x
      exact (hconv.1 x).aestronglyMeasurable
    · filter_upwards [] with x
      exact Eventually.of_forall (hbound x)
    · exact hmajor
    · filter_upwards [] with y
      have hcont : Continuous (fun x : E3 =>
          anisotropicHeatKernel B t y * f (x - y)) :=
        (continuous_const.mul (hfy y)).congr fun x => rfl
      exact hcont.continuousAt
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr hgcontAt
  have hgBound (x : E3) : ‖g x‖ ≤ ‖f‖ := by
    rw [Real.norm_eq_abs]
    exact hconv.2.1 x
  let S : E3 →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    g hgcont ‖f‖ hgBound
  refine ⟨S, ?_, ?_, ?_⟩
  · intro x
    rfl
  · exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      hgcont (norm_nonneg f) hgBound
  · intro x y
    simpa [S, g] using hconv.2.2 x y
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
