import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "V6" => EuclideanSpace ℝ (Fin 6)
/-- True Gaussian averaging preserves a uniform positive operator lower bound. -/
theorem heat_preserves_operator_coercivity (A : E3 →ᵇ (E3 →L[ℝ] E3))
    (c t : ℝ) (hc : 0<c) (ht : 0<t)
    (hA : ∀ x v : E3, c*‖v‖^2 ≤ inner ℝ (A x v) v) :
    ∀ x : E3, Integrable (fun y : E3 => euclideanHeatKernel 3 t y • A (x-y)) volume ∧
      ∀ v : E3, c*‖v‖^2 ≤ inner ℝ ((∫ y : E3, euclideanHeatKernel 3 t y • A (x-y)) v) v :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro x
  have hK : Integrable (fun y : E3 => euclideanHeatKernel 3 t y) volume :=
    (euclideanHeatKernel_mass_semigroup 3).1 t ht |>.1
  have hmass : (∫ y : E3, euclideanHeatKernel 3 t y) = 1 :=
    (euclideanHeatKernel_mass_semigroup 3).1 t ht |>.2
  have hKnonneg : ∀ y : E3, 0 ≤ euclideanHeatKernel 3 t y := by
    intro y
    exact (euclideanHeatKernel_pos 3 ht y).le
  have hAmeas : AEStronglyMeasurable (fun y : E3 => A (x - y)) volume := by
    exact (A.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hAint : Integrable
      (fun y : E3 => euclideanHeatKernel 3 t y • A (x - y)) volume := by
    apply hK.smul_bdd ‖A‖ hAmeas
    exact Eventually.of_forall (fun y => A.norm_coe_le_norm (x - y))
  refine ⟨hAint, ?_⟩
  intro v
  let L : (E3 →L[ℝ] E3) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E3 v)
  have hscalar : Integrable
      (fun y : E3 => euclideanHeatKernel 3 t y *
        inner ℝ (A (x - y) v) v) volume := by
    have hL := (ContinuousLinearMap.integral_comp_comm L hAint)
    have hL_int : Integrable
        (fun y : E3 => L (euclideanHeatKernel 3 t y • A (x - y))) volume := by
      exact L.integrable_comp hAint
    convert hL_int using 1
    funext y
    simp [L, innerSL_apply_apply, real_inner_comm]
  have hlower : Integrable
      (fun y : E3 => (c * ‖v‖ ^ 2) * euclideanHeatKernel 3 t y) volume := by
    exact hK.const_mul (c * ‖v‖ ^ 2)
  have hpoint : ∀ y : E3,
      (c * ‖v‖ ^ 2) * euclideanHeatKernel 3 t y ≤
        euclideanHeatKernel 3 t y * inner ℝ (A (x - y) v) v := by
    intro y
    have h := mul_le_mul_of_nonneg_right (hA (x - y) v) (hKnonneg y)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hint := integral_mono hlower hscalar hpoint
  have hcomm := ContinuousLinearMap.integral_comp_comm L hAint
  calc
    c * ‖v‖ ^ 2 = (c * ‖v‖ ^ 2) * 1 := by ring
    _ = (c * ‖v‖ ^ 2) * (∫ y : E3, euclideanHeatKernel 3 t y) := by rw [hmass]
    _ = ∫ y : E3, (c * ‖v‖ ^ 2) * euclideanHeatKernel 3 t y := by
      rw [integral_const_mul]
    _ ≤ ∫ y : E3, euclideanHeatKernel 3 t y *
        inner ℝ (A (x - y) v) v := hint
    _ = inner ℝ ((∫ y : E3, euclideanHeatKernel 3 t y • A (x - y)) v) v := by
      calc
        _ = ∫ y : E3, L (euclideanHeatKernel 3 t y • A (x - y)) := by
          congr 1
          funext y
          simp [L, innerSL_apply_apply, real_inner_comm]
        _ = L (∫ y : E3, euclideanHeatKernel 3 t y • A (x - y)) := hcomm
        _ = _ := by simp [L, innerSL_apply_apply, real_inner_comm]
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
