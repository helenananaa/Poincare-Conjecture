import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianCancellationThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatTimeDerivativeL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatTimeEquation
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Exact first and second coordinate moments of the actual three-dimensional kernel. -/
theorem heat_kernel_first_second_moments {t : ℝ} (ht : 0<t) :
    (∀ i : Fin 3, Integrable (fun y : E3 => euclideanHeatKernel 3 t y*y i) volume ∧
      (∫ y : E3, euclideanHeatKernel 3 t y*y i)=0) ∧
    ∀ i j : Fin 3, Integrable (fun y : E3 => euclideanHeatKernel 3 t y*y i*y j) volume ∧
      (∫ y : E3, euclideanHeatKernel 3 t y*y i*y j)=(if i=j then 2*t else 0) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : E3 → ℝ := fun y => euclideanHeatKernel 3 t y
  have hK : Integrable K volume := by
    simpa [K] using (euclideanHeatKernel_mass_semigroup 3).1 t ht |>.1
  have hKmass : (∫ y : E3, K y) = 1 := by
    simpa [K] using (euclideanHeatKernel_mass_semigroup 3).1 t ht |>.2
  have hKcont : Continuous K := by
    dsimp [K]
    unfold euclideanHeatKernel
    exact (contDiff_prod (fun k _ =>
      (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
  obtain ⟨C₁, hC₁, hmoment₁⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (1 : ℝ) (by norm_num)
  have hradial : Integrable (fun y : E3 => K y * ‖y‖) volume := by
    convert (hmoment₁ t ht).1 using 1
    simp [K, Real.rpow_one]
  have hfirst_integrable (i : Fin 3) :
      Integrable (fun y : E3 => K y * y i) volume := by
    have hcont : Continuous (fun y : E3 => K y * y i) :=
      hKcont.mul (by fun_prop)
    refine hradial.mono' hcont.aestronglyMeasurable ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (euclideanHeatKernel_pos 3 ht y).le]
    exact mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y i))
      (euclideanHeatKernel_pos 3 ht y).le
  have hfirst_zero (i : Fin 3) :
      (∫ y : E3, K y * y i) = 0 := by
    let F : E3 → ℝ := fun y => K y * y i
    have hF : Integrable F volume := by
      simpa [F] using hfirst_integrable i
    have hneg (y : E3) : F (-y) = -F y := by
      dsimp [F, K]
      have hEven : euclideanHeatKernel 3 t (-y) = euclideanHeatKernel 3 t y := by
        unfold euclideanHeatKernel
        apply Finset.prod_congr rfl
        intro k hk
        simp [gaussianHeatKernel]
      rw [hEven]
      ring
    have hchange : (∫ y : E3, F (-y)) = ∫ y : E3, F y := by
      simpa [Function.comp_def] using
        (Measure.measurePreserving_neg (volume : Measure E3)).integral_comp
          (Homeomorph.neg E3).measurableEmbedding F
    have hneg_int : (∫ y : E3, F (-y)) = -(∫ y : E3, F y) := by
      rw [show (fun y : E3 => F (-y)) = (fun y : E3 => -F y) by
        funext y
        exact hneg y, integral_neg]
    rw [hchange] at hneg_int
    linarith
  have hsecond_integrable (i j : Fin 3) :
      Integrable (fun y : E3 => K y * y i * y j) volume := by
    let H : E3 → ℝ := fun y =>
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
    have hH : Integrable H volume := by
      simpa [H] using (euclideanHeatKernel_three_hessian_cancellation ht i j).1
    have hformula (y : E3) :
        H y = (y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) * K y := by
      simpa [H, K] using euclideanHeatKernel_three_hessian_formula ht y i j
    have hcomb : Integrable (fun y : E3 =>
        4 * t ^ 2 * H y + (if i = j then 2 * t else 0) * K y) volume :=
      (hH.const_mul _).add (hK.const_mul _)
    apply hcomb.congr
    filter_upwards [] with y
    rw [hformula y]
    by_cases hij : i = j
    · simp [hij]
      field_simp [ht.ne']
      ring
    · simp [hij]
      field_simp [ht.ne']
  have hsecond_integral (i j : Fin 3) :
      (∫ y : E3, K y * y i * y j) = (if i = j then 2 * t else 0) := by
    let H : E3 → ℝ := fun y =>
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
    have hH : Integrable H volume := by
      simpa [H] using (euclideanHeatKernel_three_hessian_cancellation ht i j).1
    have hHmass : (∫ y : E3, H y) = 0 := by
      simpa [H] using (euclideanHeatKernel_three_hessian_cancellation ht i j).2
    have hformula (y : E3) :
        H y = (y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) * K y := by
      simpa [H, K] using euclideanHeatKernel_three_hessian_formula ht y i j
    have hEq : (fun y : E3 => K y * y i * y j) = (fun y : E3 =>
        4 * t ^ 2 * H y + (if i = j then 2 * t else 0) * K y) := by
      funext y
      rw [hformula y]
      by_cases hij : i = j
      · simp [hij]
        field_simp [ht.ne']
        ring
      · simp [hij]
        field_simp [ht.ne']
    rw [hEq, integral_add (hH.const_mul _) (hK.const_mul _),
      integral_const_mul, integral_const_mul, hHmass, hKmass]
    simp
  constructor
  · intro i
    exact ⟨by simpa [K] using hfirst_integrable i, by simpa [K] using hfirst_zero i⟩
  · intro i j
    exact ⟨by simpa [K] using hsecond_integrable i j,
      by simpa [K] using hsecond_integral i j⟩
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
