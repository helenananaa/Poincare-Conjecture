import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ShiftedDerivativeDominator
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual Hessian-kernel integrals depend continuously on space for bounded data. -/
theorem bounded_heat_hessian_continuous (f : E3 →ᵇ ℝ) {t : ℝ} (ht : 0 < t)
    (i j : Fin 3) : Continuous (fun x : E3 => ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*f y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rw [continuous_iff_continuousAt]
  intro x₀
  let R : ℝ := ‖x₀‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  obtain ⟨g, hg, hg_nonneg, hdom⟩ :=
    euclideanHeatKernel_three_shifted_derivative_dominator t R ht hR
  let H : E3 → ℝ := fun z =>
    fderiv ℝ (fun w : E3 => fderiv ℝ (euclideanHeatKernel 3 t) w
      (EuclideanSpace.single i 1)) z (EuclideanSpace.single j 1)
  have hH_formula : H = (fun z : E3 =>
      (z i * z j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) *
        euclideanHeatKernel 3 t z) := by
    funext z
    exact euclideanHeatKernel_three_hessian_formula ht z i j
  have hKcont : Continuous (fun z : E3 => euclideanHeatKernel 3 t z) := by
    unfold euclideanHeatKernel
    exact (contDiff_prod (fun k _ =>
      (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
  have hcoef : Continuous (fun z : E3 =>
      z i * z j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) := by
    fun_prop
  have hHcont : Continuous H := by
    rw [hH_formula]
    exact hcoef.mul hKcont
  let F : E3 → E3 → ℝ := fun x y => H (x - y) * f y
  have hF_meas (x : E3) : AEStronglyMeasurable (F x) volume := by
    have hF_cont : Continuous (fun y : E3 => F x y) := by
      dsimp [F]
      exact (hHcont.comp (continuous_const.sub continuous_id)).mul f.continuous
    exact hF_cont.aestronglyMeasurable
  have hF_cont (y : E3) : Continuous (fun x : E3 => F x y) := by
    dsimp [F]
    exact (hHcont.comp (continuous_id.sub continuous_const)).mul continuous_const
  let s : Set E3 := Metric.closedBall 0 R
  have hball (x : E3) (hx : x ∈ s) : ‖x‖ ≤ R := by
    simpa [s, Metric.mem_closedBall, dist_eq_norm] using hx
  have hx₀ : x₀ ∈ s := by
    rw [show s = Metric.closedBall 0 R by rfl, Metric.mem_closedBall]
    dsimp [s, R]
    simpa [dist_eq_norm] using (le_add_of_nonneg_right (norm_nonneg x₀))
  have hs_nhds : s ∈ 𝓝 x₀ := by
    apply Metric.mem_nhds_iff.2
    refine ⟨1, one_pos, ?_⟩
    intro z hz
    change dist z x₀ < 1 at hz
    rw [show s = Metric.closedBall 0 R by rfl, Metric.mem_closedBall]
    calc
      dist z 0 ≤ dist z x₀ + dist x₀ 0 := dist_triangle _ _ _
      _ ≤ 1 + ‖x₀‖ := by
        rw [dist_zero_right]
        simpa [add_comm] using (add_le_add_right hz.le ‖x₀‖)
      _ ≤ R := by
        dsimp [R]
        simpa [add_comm]
  have hbound (x : E3) (hx : x ∈ s) :
      ∀ᵐ y ∂volume, ‖F x y‖ ≤ ‖f‖ * g y := by
    filter_upwards [] with y
    have hHdom : |H (x - y)| ≤ g y := by
      change |fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) (x - y) (EuclideanSpace.single j 1)| ≤ g y
      exact (hdom x y (hball x hx)).2.2 i j
    have hf : |f y| ≤ ‖f‖ := by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y
    dsimp [F]
    rw [abs_mul]
    calc
      |H (x - y)| * |f y| ≤ g y * ‖f‖ :=
        mul_le_mul hHdom hf (abs_nonneg _) (hg_nonneg y)
      _ = ‖f‖ * g y := by ring
  have hcont : ∀ᵐ y ∂volume, ContinuousOn (fun x : E3 => F x y) s := by
    filter_upwards [] with y
    exact (hF_cont y).continuousOn
  have hInt : ContinuousOn (fun x : E3 => ∫ y : E3, F x y) s := by
    apply continuousOn_of_dominated (s := s)
    · intro x hx
      exact hF_meas x
    · intro x hx
      exact hbound x hx
    · exact hg.const_mul ‖f‖
    · exact hcont
  have hAt := (hInt.continuousWithinAt hx₀).continuousAt hs_nhds
  simpa [F, H] using hAt
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
