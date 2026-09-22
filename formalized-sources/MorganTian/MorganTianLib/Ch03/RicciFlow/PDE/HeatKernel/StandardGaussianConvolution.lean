import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedClassicalIVP
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedDuhamelNonlinearDifference
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelBoundedForcing
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideTranslationL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter Function
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "HeatSpace" => (ℝ × E3) →ᵇ ℝ
/-- Exact nonsingular representation of actual convolution using a fixed Gaussian. -/
theorem heat_convolution_standard_gaussian (f : E3 →ᵇ ℝ) (t : ℝ) (ht : 0 < t) (x : E3) :
    (∫ y : E3, euclideanHeatKernel 3 t y * f (x-y)) =
      ∫ z : E3, euclideanHeatKernel 3 1 z * f (x-(Real.sqrt t) • z) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let s : ℝ := Real.sqrt t
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 ht
  have hsne : s ≠ 0 := ne_of_gt hs
  have hs_sq : s ^ 2 = t := by
    dsimp [s]
    exact Real.sq_sqrt ht.le
  have hsqrt4 : Real.sqrt (4 * Real.pi * t) = Real.sqrt (4 * Real.pi) * s := by
    dsimp [s]
    rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring,
      Real.sqrt_mul (by positivity)]
  have hscale (z : E3) :
      euclideanHeatKernel 3 t (s • z) = s⁻¹ ^ (3 : ℕ) * euclideanHeatKernel 3 1 z := by
    rw [euclideanHeatKernel_three_norm_form, euclideanHeatKernel_three_norm_form]
    have hnorm : ‖s • z‖ ^ 2 = t * ‖z‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, hs_sq]
    have hexp : -‖s • z‖ ^ 2 / (4 * t) = -‖z‖ ^ 2 / (4 * (1 : ℝ)) := by
      rw [hnorm]
      field_simp [ht.ne']
    rw [hsqrt4, hexp]
    have hroot4 : Real.sqrt (4 * Real.pi) ≠ 0 := by
      positivity
    field_simp [hsne, hroot4]
  let F : E3 → ℝ := fun y => euclideanHeatKernel 3 t y * f (x - y)
  have hF : Integrable F volume := by
    have hk : Integrable (euclideanHeatKernel 3 t) (volume : Measure E3) :=
      (euclideanHeatKernel_mass_semigroup 3).1 t ht |>.1
    have hmeas : AEStronglyMeasurable (fun y : E3 => f (x - y)) volume := by
      fun_prop
    dsimp [F]
    exact hk.mul_bdd hmeas (Eventually.of_forall (fun y => f.norm_coe_le_norm (x - y)))
  have hcomp : (fun z : E3 => euclideanHeatKernel 3 1 z * f (x - s • z)) =
      (fun z : E3 => s ^ (3 : ℕ) * F (s • z)) := by
    funext z
    dsimp [F]
    rw [hscale z]
    field_simp [hsne]
  have hFcomp : Integrable (fun z : E3 => F (s • z)) volume :=
    hF.comp_smul hsne
  have hchange : (∫ z : E3, F (s • z)) =
      (s ^ (3 : ℕ))⁻¹ * ∫ y : E3, F y := by
    have hdim : Module.finrank ℝ E3 = 3 := by simp
    simpa [smul_eq_mul, hdim] using
      (Measure.integral_comp_smul_of_nonneg (volume : Measure E3) F s (hR := hs.le))
  calc
    (∫ y : E3, euclideanHeatKernel 3 t y * f (x - y)) = ∫ y : E3, F y := by rfl
    _ = s ^ (3 : ℕ) * ((s ^ (3 : ℕ))⁻¹ * ∫ y : E3, F y) := by
      field_simp [hsne]
    _ = s ^ (3 : ℕ) * (∫ z : E3, F (s • z)) := by rw [hchange]
    _ = ∫ z : E3, s ^ (3 : ℕ) * F (s • z) := by
      rw [integral_const_mul]
    _ = ∫ z : E3, euclideanHeatKernel 3 1 z * f (x - s • z) := by rw [hcomp]
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
