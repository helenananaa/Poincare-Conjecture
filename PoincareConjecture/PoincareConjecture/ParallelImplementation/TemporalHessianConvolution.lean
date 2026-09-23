import PoincareConjecture.ParallelImplementation.TemporalHessianL1Modulus
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.TemporalHessianConvolution
open MorganTianLib.MetricCoefficient
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Time modulus after cancellation against an actual spatially Holder forcing. -/
theorem heatHessian_convolution_time_modulus
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E3 →ᵇ ℝ) (L : ℝ), 0 ≤ L →
      (∀ x z : E3, |f x-f z| ≤ L*‖x-z‖^alpha) →
      ∀ t h : ℝ, 0 < t → 0 < h → ∀ (x : E3) (i j : Fin 3),
      |∫ y : E3, (heatHessian3 (t+h) i j y - heatHessian3 t i j y) * f (x-y)| ≤
        C * L * min (t^(alpha/2-1)) (h*t^(alpha/2-2)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, hmod⟩ :=
    PoincareConjecture.ParallelImplementation.TemporalHessianL1Modulus.heatHessian_time_difference_L1_modulus
      alpha ha ha1
  obtain ⟨_, _, hspatial⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_holder_hessian_convolution
      alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro f L hL hholder t h ht hh x i j
  let K : ℝ → E3 → ℝ := fun s y => heatHessian3 s i j y
  let D : E3 → ℝ := fun y => K (t + h) y - K t y
  have hcancel (s : ℝ) (hs : 0 < s) :
      Integrable (fun y : E3 => heatHessian3 s i j y) volume ∧
        (∫ y : E3, heatHessian3 s i j y) = 0 := by
    simpa [heatHessian3] using
      MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_hessian_cancellation hs i j
  have hcancelPlus := hcancel (t + h) (by linarith)
  have hcancelBase := hcancel t ht
  have hDInt : Integrable D volume := by
    dsimp [D, K]
    exact hcancelPlus.1.sub hcancelBase.1
  have hDmass : (∫ y : E3, D y) = 0 := by
    dsimp [D, K]
    rw [integral_sub hcancelPlus.1 hcancelBase.1, hcancelPlus.2, hcancelBase.2]
    simp
  have hplusF : Integrable (fun y : E3 => heatHessian3 (t + h) i j y * f (x - y)) volume := by
    simpa [heatHessian3] using
      (hspatial f L hL hholder (t + h) (by linarith) i j x).1
  have hbaseF : Integrable (fun y : E3 => heatHessian3 t i j y * f (x - y)) volume := by
    simpa [heatHessian3] using
      (hspatial f L hL hholder t ht i j x).1
  have hfullInt : Integrable (fun y : E3 => D y * f (x - y)) volume := by
    have hsub := hplusF.sub hbaseF
    convert hsub using 1
    funext y
    simp [D, K]
    ring
  have hconstInt : Integrable (fun y : E3 => D y * f x) volume :=
    hDInt.mul_const (f x)
  have hsubInt : Integrable (fun y : E3 => D y * (f (x - y) - f x)) volume := by
    have heq : (fun y : E3 => D y * (f (x - y) - f x)) =
        (fun y => D y * f (x - y) - D y * f x) := by
      funext y
      ring
    rw [heq]
    exact hfullInt.sub hconstInt
  have hsubtract :
      (∫ y : E3, D y * f (x - y)) =
        ∫ y : E3, D y * (f (x - y) - f x) := by
    calc
      (∫ y : E3, D y * f (x - y)) =
          ∫ y : E3, (D y * (f (x - y) - f x)) + D y * f x :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
      _ = (∫ y : E3, D y * (f (x - y) - f x)) +
          ∫ y : E3, D y * f x := integral_add hsubInt hconstInt
      _ = (∫ y : E3, D y * (f (x - y) - f x)) +
          (∫ y : E3, D y) * f x := by rw [integral_mul_const]
      _ = ∫ y : E3, D y * (f (x - y) - f x) := by rw [hDmass]; simp
  obtain ⟨hweightI, hweightB⟩ := hmod t h ht hh i j
  have hweightI' : Integrable (fun y : E3 => |D y| * ‖y‖ ^ alpha) volume := by
    simpa [D, K] using hweightI
  have hweightB' :
      (∫ y : E3, |D y| * ‖y‖ ^ alpha) ≤ C * min (t ^ (alpha / 2 - 1))
        (h * t ^ (alpha / 2 - 2)) := by
    simpa [D, K] using hweightB
  have hmajorI : Integrable (fun y : E3 => L * (|D y| * ‖y‖ ^ alpha)) volume :=
    hweightI'.const_mul L
  have hpoint (y : E3) :
      ‖D y * (f (x - y) - f x)‖ ≤ L * (|D y| * ‖y‖ ^ alpha) := by
    have hholder' : |f (x - y) - f x| ≤ L * ‖y‖ ^ alpha := by
      have hnorm : ‖(x - y) - x‖ = ‖y‖ := by
        rw [show (x - y) - x = -y by abel, norm_neg]
      simpa [hnorm] using hholder (x - y) x
    calc
      ‖D y * (f (x - y) - f x)‖ = |D y| * |f (x - y) - f x| := by
        simp [Real.norm_eq_abs]
      _ ≤ |D y| * (L * ‖y‖ ^ alpha) :=
        mul_le_mul_of_nonneg_left hholder' (abs_nonneg _)
      _ = L * (|D y| * ‖y‖ ^ alpha) := by ring
  have hnormBound :
      ‖∫ y : E3, D y * (f (x - y) - f x)‖ ≤
        ∫ y : E3, L * (|D y| * ‖y‖ ^ alpha) :=
    norm_integral_le_of_norm_le hmajorI (Filter.Eventually.of_forall hpoint)
  have hcore :
      |∫ y : E3, D y * (f (x - y) - f x)| ≤
        L * (∫ y : E3, |D y| * ‖y‖ ^ alpha) := by
    simpa only [Real.norm_eq_abs, integral_const_mul] using hnormBound
  calc
    |∫ y : E3, (heatHessian3 (t + h) i j y - heatHessian3 t i j y) * f (x - y)| =
        |∫ y : E3, D y * (f (x - y) - f x)| := by
      simpa [D, K] using congrArg (fun z : ℝ => |z|) hsubtract
    _ ≤ L * (∫ y : E3, |D y| * ‖y‖ ^ alpha) := hcore
    _ ≤ L * (C * min (t ^ (alpha / 2 - 1)) (h * t ^ (alpha / 2 - 2))) :=
      mul_le_mul_of_nonneg_left hweightB' hL
    _ = C * L * min (t ^ (alpha / 2 - 1)) (h * t ^ (alpha / 2 - 2)) := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.TemporalHessianConvolution
