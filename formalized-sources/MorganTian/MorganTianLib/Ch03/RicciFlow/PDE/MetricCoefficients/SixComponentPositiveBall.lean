import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseQuadraticRemainder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PrincipalPartDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- A concrete component-space radius preserves positive metric coefficients. -/
theorem six_component_positive_neighborhood :
    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖≤3 ∧
      (∀ (q : E6) (v : E3) (i : Fin 3), (E q v) i = ∑ j : Fin 3, symmetricSixMatrix q i j*v j) ∧
      ∀ (q0 q : E6) (c : ℝ), 0<c →
        (∀ v : E3, c*‖v‖^2 ≤ inner ℝ (E q0 v) v) → ‖q-q0‖≤c/6 →
        (∀ v : E3, (c/2)*‖v‖^2 ≤ inner ℝ (E q v) v) ∧
        ∃ e : E3 ≃L[ℝ] E3, e.toContinuousLinearMap=E q ∧ ‖e.symm.toContinuousLinearMap‖≤2/c :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨E, hE_inj, hE_norm, hE_action, _⟩ := symmetric_six_realization
  refine ⟨E, hE_inj, hE_norm, hE_action, ?_⟩
  intro q0 q c hc hq0 hqq
  have hdiff : ‖E q - E q0‖ ≤ c / 2 := by
    calc
      ‖E q - E q0‖ = ‖E (q - q0)‖ := by rw [map_sub]
      _ ≤ ‖E‖ * ‖q - q0‖ := E.le_opNorm _
      _ ≤ 3 * ‖q - q0‖ := by gcongr
      _ ≤ 3 * (c / 6) := by gcongr
      _ = c / 2 := by ring
  have hA : ‖E q0 - E q0‖ ≤ c / 2 := by
    simp only [sub_self, norm_zero]
    positivity
  have hEq : ∀ v : E3, (c / 2) * ‖v‖ ^ 2 ≤ inner ℝ (E q v) v :=
    coercivity_survives_operator_perturbation (E q0) (E q) c hc hq0 hdiff
  obtain ⟨a, b, ha, hb, ha_bound, hb_bound, _⟩ :=
    positive_ball_inverse_control (E q0) c hc hq0 (E q0) (E q) hA hdiff
  exact ⟨hEq, ⟨b, hb, hb_bound⟩⟩
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
