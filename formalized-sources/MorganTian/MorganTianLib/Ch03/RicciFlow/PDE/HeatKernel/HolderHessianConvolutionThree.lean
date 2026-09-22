import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianCancellationThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianEstimate
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianCancellation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- A genuine Holder-to-Hessian convolution estimate, using cancellation. -/
theorem euclideanHeatKernel_three_holder_hessian_convolution (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E3 →ᵇ ℝ) (L : ℝ), 0 ≤ L →
      (∀ x y : E3, |f x-f y| ≤ L*‖x-y‖^alpha) →
      ∀ t : ℝ, 0 < t → ∀ (i j : Fin 3) (x : E3),
        Integrable (fun y : E3 => (fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)) * f (x-y)) volume ∧
        |∫ y : E3, (fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)) * f (x-y)| ≤ C*L*t^(alpha/2-1) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, hbound⟩ :=
    euclideanHeatKernel_three_weighted_hessian_recursive alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro f L hL hholder t ht i j x
  obtain ⟨hhess, hmass⟩ := euclideanHeatKernel_three_hessian_cancellation ht i j
  obtain ⟨hweight, hweight_bound⟩ := hbound t ht i j
  let H : E3 → ℝ := fun y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
  have hH_eq (y : E3) : H y =
      (y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) *
        euclideanHeatKernel 3 t y := by
    exact euclideanHeatKernel_three_hessian_formula ht y i j
  have hH_cont : Continuous H := by
    rw [show H = (fun y : E3 =>
        (y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) *
          euclideanHeatKernel 3 t y) by
      funext y
      exact hH_eq y]
    have hKcont : Continuous (fun y : E3 => euclideanHeatKernel 3 t y) := by
      unfold euclideanHeatKernel
      exact (contDiff_prod (fun k _ =>
        (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
    have hcoef : Continuous (fun y : E3 =>
        y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) := by
      fun_prop
    exact hcoef.mul hKcont
  let difference : E3 → ℝ := fun y => H y * (f (x - y) - f x)
  have hdiff_cont : Continuous difference := by
    dsimp [difference]
    exact hH_cont.mul (f.continuous.comp (continuous_const.sub continuous_id) |>.sub
      continuous_const)
  have hdiff_dom : Integrable
      (fun y : E3 => L * (|H y| * ‖y‖ ^ alpha)) volume :=
    hweight.const_mul L
  have hdiff_bound : ∀ y : E3,
      ‖difference y‖ ≤ L * (|H y| * ‖y‖ ^ alpha) := by
    intro y
    have hxy : |f (x - y) - f x| ≤ L * ‖y‖ ^ alpha := by
      have hy : ‖(x - y) - x‖ ^ alpha = ‖y‖ ^ alpha := by
        rw [show (x - y) - x = -y by abel, norm_neg]
      simpa only [hy] using hholder (x - y) x
    dsimp [difference]
    rw [abs_mul]
    calc
      |H y| * |f (x - y) - f x| ≤ |H y| * (L * ‖y‖ ^ alpha) :=
        mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
      _ = L * (|H y| * ‖y‖ ^ alpha) := by ring
  have hdiff_int : Integrable difference volume := by
    apply hdiff_dom.mono' hdiff_cont.aestronglyMeasurable
    filter_upwards [] with y
    exact hdiff_bound y
  have hconst_int : Integrable (fun y : E3 => H y * f x) volume :=
    hhess.mul_const _
  have hfull_int : Integrable
      (fun y : E3 => H y * f (x - y)) volume := by
    have hdecomp :
        (fun y : E3 => H y * f (x - y)) =
          (fun y : E3 => difference y + H y * f x) := by
      funext y
      dsimp [difference]
      ring
    rw [hdecomp]
    exact hdiff_int.add hconst_int
  have hconst_value : (∫ y : E3, H y * f x) = 0 := by
    rw [integral_mul_const, hmass]
    ring
  have hrewrite :
      (∫ y : E3, H y * f (x - y)) = ∫ y : E3, difference y := by
    have hdecomp :
        (fun y : E3 => H y * f (x - y)) =
          (fun y : E3 => difference y + H y * f x) := by
      funext y
      dsimp [difference]
      ring
    calc
      (∫ y : E3, H y * f (x - y)) =
          ∫ y : E3, (difference y + H y * f x) := by rw [hdecomp]
      _ = (∫ y : E3, difference y) + ∫ y : E3, H y * f x :=
        integral_add hdiff_int hconst_int
      _ = ∫ y : E3, difference y := by rw [hconst_value, add_zero]
  refine ⟨hfull_int, ?_⟩
  calc
    |(∫ y : E3, H y * f (x - y))| = ‖∫ y : E3, difference y‖ := by
      rw [hrewrite]
      rfl
    _ ≤ ∫ y : E3, L * (|H y| * ‖y‖ ^ alpha) :=
      norm_integral_le_of_norm_le hdiff_dom (Eventually.of_forall hdiff_bound)
    _ = L * (∫ y : E3, |H y| * ‖y‖ ^ alpha) := by
      rw [integral_const_mul]
    _ ≤ L * (C * t ^ (alpha / 2 - 1)) :=
      mul_le_mul_of_nonneg_left hweight_bound hL
    _ = C * L * t ^ (alpha / 2 - 1) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
