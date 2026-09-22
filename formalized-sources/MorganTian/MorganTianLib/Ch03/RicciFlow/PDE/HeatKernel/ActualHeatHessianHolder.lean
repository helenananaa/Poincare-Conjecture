import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderHessianConvolutionThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianEstimate
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideHessianUnweighted
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatTimeDerivativeL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalInitialTrace
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ShiftedDerivativeDominator
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual Hessian entries preserve a spatial Holder modulus with a positive-time cost. -/
theorem actual_heat_hessian_spatial_holder (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E3 →ᵇ ℝ) (L : ℝ), 0 ≤ L →
      (∀ x y : E3, |f x-f y| ≤ L*‖x-y‖^alpha) → ∀ t : ℝ, 0 < t →
        let u : E3 → ℝ := fun x => ∫ y : E3, euclideanHeatKernel 3 t (x-y)*f y
        ∀ (x z : E3) (i j : Fin 3),
          |fderiv ℝ (fun w : E3 => fderiv ℝ u w (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) -
            fderiv ℝ (fun w : E3 => fderiv ℝ u w (EuclideanSpace.single i 1)) z (EuclideanSpace.single j 1)|
              ≤ C*L*‖x-z‖^alpha/t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, hL1⟩ := euclideanHeatKernel_three_hessian_L1
  refine ⟨C, hC, ?_⟩
  intro f L hL hholder t ht
  dsimp
  intro x z i j
  let H : E3 → ℝ := fun y =>
    fderiv ℝ (fun w : E3 => fderiv ℝ (euclideanHeatKernel 3 t) w
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
  have hH_int : Integrable H volume := by
    simpa [H] using (hL1 t ht i j).1
  have hH_bound : (∫ y : E3, |H y|) ≤ C / t := by
    simpa [H] using (hL1 t ht i j).2
  have hfcomp (a : E3) :
      AEStronglyMeasurable (fun y : E3 => f (a - y)) volume := by
    exact (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hconv (a : E3) :
      Integrable (fun y : E3 => H y * f (a - y)) volume := by
    apply hH_int.mul_bdd (hfcomp a)
    exact Eventually.of_forall (fun y => f.norm_coe_le_norm (a - y))
  have hmajor : Integrable
      (fun y : E3 => (L * ‖x - z‖ ^ alpha) * |H y|) volume := by
    simpa [Real.norm_eq_abs, mul_comm] using
      hH_int.norm.const_mul (L * ‖x - z‖ ^ alpha)
  have hdiff_bound : ∀ y : E3,
      ‖H y * (f (x - y) - f (z - y))‖ ≤
        (L * ‖x - z‖ ^ alpha) * |H y| := by
    intro y
    have hxy : |f (x - y) - f (z - y)| ≤ L * ‖x - z‖ ^ alpha := by
      simpa only [show (x - y) - (z - y) = x - z by abel] using
        hholder (x - y) (z - y)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |H y| * |f (x - y) - f (z - y)| ≤
          |H y| * (L * ‖x - z‖ ^ alpha) :=
        mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
      _ = (L * ‖x - z‖ ^ alpha) * |H y| := by ring
  have hix :
      fderiv ℝ (fun w : E3 => fderiv ℝ
        (fun q : E3 => ∫ y : E3,
          euclideanHeatKernel 3 t (q-y) * f y) w
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
        ∫ y : E3, H y * f (x-y) := by
    simpa [H] using
      (euclideanHeatKernel_bounded_hessian_identification f ht).2 x i j
  have hiz :
      fderiv ℝ (fun w : E3 => fderiv ℝ
        (fun q : E3 => ∫ y : E3,
          euclideanHeatKernel 3 t (q-y) * f y) w
          (EuclideanSpace.single i 1)) z (EuclideanSpace.single j 1) =
        ∫ y : E3, H y * f (z-y) := by
    simpa [H] using
      (euclideanHeatKernel_bounded_hessian_identification f ht).2 z i j
  rw [hix, hiz, ← integral_sub (hconv x) (hconv z)]
  have hrewrite :
      (fun y : E3 => H y * f (x-y) - H y * f (z-y)) =
        (fun y : E3 => H y * (f (x-y) - f (z-y))) := by
    funext y
    ring
  rw [show (∫ y : E3, H y * f (x-y) - H y * f (z-y)) =
      ∫ y : E3, H y * (f (x-y) - f (z-y)) by rw [hrewrite]]
  calc
    |∫ y : E3, H y * (f (x-y) - f (z-y))| ≤
        ∫ y : E3, (L * ‖x-z‖ ^ alpha) * |H y| :=
      norm_integral_le_of_norm_le hmajor (Eventually.of_forall hdiff_bound)
    _ = (L * ‖x-z‖ ^ alpha) * (∫ y : E3, |H y|) := by
      rw [integral_const_mul]
    _ ≤ (L * ‖x-z‖ ^ alpha) * (C / t) := by
      exact mul_le_mul_of_nonneg_left hH_bound (by positivity)
    _ = C * L * ‖x-z‖ ^ alpha / t := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
