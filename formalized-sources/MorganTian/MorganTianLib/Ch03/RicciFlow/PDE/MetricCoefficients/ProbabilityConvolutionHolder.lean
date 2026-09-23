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

/-- **Math.** probability convolution holder. -/
theorem probability_convolution_holder (K : E3 → ℝ) (hK : Integrable K volume) (hKpos : ∀ x, 0 ≤ K x)
    (hMass : (∫ x : E3, K x) = 1) (f : E3 →ᵇ ℝ) (alpha H : ℝ) (hH : 0 ≤ H)
    (hf : ∀ x y : E3, |f x-f y| ≤ H*‖x-y‖^alpha) :
    (∀ x : E3, Integrable (fun y : E3 => K y*f (x-y)) volume) ∧
      (∀ x : E3, |∫ y : E3, K y*f (x-y)| ≤ ‖f‖) ∧
      ∀ x z : E3, |(∫ y : E3, K y*f (x-y))-(∫ y : E3, K y*f (z-y))| ≤ H*‖x-z‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  have hcont (x : E3) : Continuous (fun y : E3 => f (x - y)) :=
    f.continuous.comp (continuous_const.sub continuous_id)
  have hmajor (c : ℝ) : Integrable (fun y : E3 => K y * c) volume :=
    hK.mul_const c
  have hbound (x y : E3) : ‖K y * f (x - y)‖ ≤ K y * ‖f‖ := by
    calc
      ‖K y * f (x - y)‖ = K y * ‖f (x - y)‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hKpos y)]
      _ ≤ K y * ‖f‖ := mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (hKpos y)
  have hint (x : E3) : Integrable (fun y : E3 => K y * f (x - y)) volume := by
    apply Integrable.mono' (hmajor ‖f‖)
      (hK.aestronglyMeasurable.mul (hcont x).aestronglyMeasurable)
    exact Eventually.of_forall (hbound x)
  refine ⟨hint, ?_, ?_⟩
  · intro x
    calc
      |∫ y : E3, K y * f (x - y)| = ‖∫ y : E3, K y * f (x - y)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ y : E3, K y * ‖f‖ :=
        norm_integral_le_of_norm_le (hmajor ‖f‖) (Eventually.of_forall (hbound x))
      _ = ‖f‖ := by
        rw [integral_mul_const ‖f‖ K, hMass]
        simp
  · intro x z
    let c : ℝ := H * ‖x - z‖ ^ alpha
    have hdiffBound (y : E3) :
        ‖K y * f (x - y) - K y * f (z - y)‖ ≤ K y * c := by
      calc
        ‖K y * f (x - y) - K y * f (z - y)‖ =
            K y * |f (x - y) - f (z - y)| := by
          rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hKpos y),
            Real.norm_eq_abs]
        _ ≤ K y * (H * ‖(x - y) - (z - y)‖ ^ alpha) :=
          mul_le_mul_of_nonneg_left (hf (x - y) (z - y)) (hKpos y)
        _ = K y * c := by
          dsimp [c]
          rw [show (x - y) - (z - y) = x - z by abel]
    calc
      |(∫ y : E3, K y * f (x - y)) - (∫ y : E3, K y * f (z - y))| =
          ‖∫ y : E3, (K y * f (x - y) - K y * f (z - y))‖ := by
        rw [← integral_sub (hint x) (hint z)]
        exact (Real.norm_eq_abs _).symm
      _ ≤ ∫ y : E3, K y * c :=
        norm_integral_le_of_norm_le (hmajor c) (Eventually.of_forall hdiffBound)
      _ = c := by
        rw [integral_mul_const c K, hMass]
        simp [c]
      _ = H * ‖x - z‖ ^ alpha := rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
