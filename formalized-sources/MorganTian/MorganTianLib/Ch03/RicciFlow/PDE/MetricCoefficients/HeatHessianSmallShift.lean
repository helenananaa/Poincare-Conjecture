import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianHessianTranslation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianCancellationThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** heat hessian small shift. -/
theorem heat_hessian_small_shift 
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E3 →ᵇ ℝ) (L : ℝ), 0 ≤ L →
      (∀ x z : E3, |f x-f z| ≤ L*‖x-z‖^alpha) → ∀ t : ℝ, 0 < t →
      ∀ (x z : E3), ‖x-z‖ ≤ Real.sqrt t → ∀ i j : Fin 3,
      |(∫ y : E3, heatHessian3 t i j y*f (x-y))-(∫ y : E3, heatHessian3 t i j y*f (z-y))| ≤
        C*L*‖x-z‖*t^(alpha/2-3/2) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, htrans⟩ := gaussian_hessian_weighted_translation alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro f L hL hholder t ht x z hxz i j
  let H : E3 → ℝ := heatHessian3 t i j
  let h : E3 := x - z
  let delta : E3 → ℝ := fun y => H (y + h) - H y
  let g : E3 → ℝ := fun y => delta y * (f (z - y) - f z)
  obtain ⟨hHint, hHmass⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_hessian_cancellation ht i j
  have hHintegrable : Integrable H volume := by
    change Integrable (heatHessian3 t i j) volume
    exact hHint
  have hHmass' : (∫ y : E3, H y) = 0 := by
    change (∫ y : E3, heatHessian3 t i j y) = 0
    exact hHmass
  have hHshift : Integrable (fun y : E3 => H (y + h)) volume := by
    have hh :=
      (measurePreserving_add_right (volume : Measure E3) h).integrable_comp_of_integrable
        hHintegrable
    simpa [Function.comp_def] using hh
  have hdeltaInt : Integrable delta volume := by
    change Integrable (fun y : E3 => H (y + h) - H y) volume
    exact hHshift.sub hHintegrable
  have hmassShift : (∫ y : E3, H (y + h)) = ∫ y : E3, H y := by
    simpa [Function.comp_def] using
      (measurePreserving_add_right (volume : Measure E3) h).integral_comp
        (measurableEmbedding_addRight h) H
  have hdeltaMass : (∫ y : E3, delta y) = 0 := by
    calc
      (∫ y : E3, delta y) = (∫ y : E3, H (y + h)) - ∫ y : E3, H y := by
        simp [delta, integral_sub hHshift hHintegrable]
      _ = 0 := by rw [hmassShift, hHmass']; ring
  obtain ⟨hweightInt, hweightBound⟩ := htrans t ht h (by simpa [h] using hxz) i j
  have hmajor : Integrable (fun y : E3 => L *
      (|delta y| * ‖y‖ ^ alpha)) volume := by
    simpa [delta, mul_comm] using hweightInt.const_mul L
  have hpoint : ∀ y : E3, ‖g y‖ ≤ L * (|delta y| * ‖y‖ ^ alpha) := by
    intro y
    have hy : ‖(z - y) - z‖ ^ alpha = ‖y‖ ^ alpha := by
      rw [show (z - y) - z = -y by abel, norm_neg]
    have hfy : |f (z - y) - f z| ≤ L * ‖y‖ ^ alpha := by
      simpa only [hy] using hholder (z - y) z
    dsimp [g, delta]
    rw [abs_mul]
    calc
      |H (y + h) - H y| * |f (z - y) - f z| ≤
          |H (y + h) - H y| * (L * ‖y‖ ^ alpha) :=
        mul_le_mul_of_nonneg_left hfy (abs_nonneg _)
      _ = L * (|H (y + h) - H y| * ‖y‖ ^ alpha) := by ring
  have hfcomp (a : E3) : AEStronglyMeasurable (fun y : E3 => f (a - y)) volume := by
    exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  have hconv (a : E3) : Integrable (fun y : E3 => H y * f (a - y)) volume := by
    apply hHintegrable.mul_bdd (hfcomp a)
    exact Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm (a - y))
  have hshiftConv : Integrable (fun y : E3 => H (y + h) * f (z - y)) volume := by
    apply hHshift.mul_bdd (hfcomp z)
    exact Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm (z - y))
  have hfdiff : AEStronglyMeasurable (fun y : E3 => f (z - y) - f z) volume := by
    exact ((f.continuous.comp (by fun_prop)).sub continuous_const).aestronglyMeasurable
  have hfdiffBound : ∀ y : E3, ‖f (z - y) - f z‖ ≤ 2 * ‖f‖ := by
    intro y
    calc
      ‖f (z - y) - f z‖ ≤ ‖f (z - y)‖ + ‖f z‖ := norm_sub_le _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
      _ = 2 * ‖f‖ := by ring
  have hgInt : Integrable g volume := by
    apply hdeltaInt.mul_bdd hfdiff
    exact Filter.Eventually.of_forall (fun y => hfdiffBound y)
  have hconstantInt : Integrable (fun y : E3 => delta y * f z) volume :=
    hdeltaInt.mul_const (f z)
  have hqInt : Integrable (fun y : E3 => delta y * f (z - y)) volume := by
    have hdecomp : (fun y : E3 => delta y * f (z - y)) =
        fun y => g y + delta y * f z := by
      funext y
      dsimp [g]
      ring
    rw [hdecomp]
    exact hgInt.add hconstantInt
  have hconstantIntegral : (∫ y : E3, delta y * f z) = 0 := by
    rw [integral_mul_const, hdeltaMass]
    ring
  have hqToG : (∫ y : E3, delta y * f (z - y)) = ∫ y : E3, g y := by
    have hdecomp : (fun y : E3 => delta y * f (z - y)) =
        fun y => g y + delta y * f z := by
      funext y
      dsimp [g]
      ring
    calc
      (∫ y : E3, delta y * f (z - y)) =
          (∫ y : E3, g y + delta y * f z) := by rw [hdecomp]
      _ = (∫ y : E3, g y) + ∫ y : E3, delta y * f z :=
        integral_add hgInt hconstantInt
      _ = ∫ y : E3, g y := by rw [hconstantIntegral, add_zero]
  have hchange :
      (∫ y : E3, H y * f (x - y)) - ∫ y : E3, H y * f (z - y) =
        ∫ y : E3, delta y * f (z - y) := by
    have hcomp :=
      (measurePreserving_add_right (volume : Measure E3) h).integral_comp
        (measurableEmbedding_addRight h)
        (fun y : E3 => H y * f (x - y))
    have htranslate :
        (∫ y : E3, H y * f (x - y)) =
          ∫ y : E3, H (y + h) * f (z - y) := by
      have hpointwise : (fun y : E3 => H (y + h) * f (z - y)) =
          fun y => (fun u : E3 => H u * f (x - u)) (y + h) := by
        funext y
        dsimp [h]
        congr 1
        abel
      calc
        (∫ y : E3, H y * f (x - y)) =
            ∫ y : E3, (fun u : E3 => H u * f (x - u)) (y + h) := by
              symm
              exact hcomp
        _ = ∫ y : E3, H (y + h) * f (z - y) := by rw [hpointwise]
    calc
      _ = (∫ y : E3, H (y + h) * f (z - y)) -
          ∫ y : E3, H y * f (z - y) := by rw [htranslate]
      _ = ∫ y : E3, (H (y + h) * f (z - y) - H y * f (z - y)) := by
        rw [← integral_sub hshiftConv (hconv z)]
      _ = ∫ y : E3, delta y * f (z - y) := by
        congr 1
        funext y
        dsimp [delta]
        ring
  rw [hchange, hqToG]
  calc
    |∫ y : E3, g y| ≤ ∫ y : E3, L * (|delta y| * ‖y‖ ^ alpha) := by
      exact norm_integral_le_of_norm_le hmajor (Filter.Eventually.of_forall hpoint)
    _ = L * (∫ y : E3, |delta y| * ‖y‖ ^ alpha) := by rw [integral_const_mul]
    _ ≤ L * (C * ‖h‖ * t ^ (alpha / 2 - 3 / 2)) := by
      exact mul_le_mul_of_nonneg_left hweightBound hL
    _ = C * L * ‖x - z‖ * t ^ (alpha / 2 - 3 / 2) := by
      dsimp [h]
      ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
