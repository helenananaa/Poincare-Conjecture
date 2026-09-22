import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoerciveInverse
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifference
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PositivePerturbation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function
open scoped Topology RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual inverse coefficients exist throughout a positive neighborhood and vary Lipschitzly there. -/
theorem positive_ball_inverse_control (A0 : E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA0 : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A0 v) v)
    (A B : E3 →L[ℝ] E3) (hA : ‖A-A0‖ ≤ c/2) (hB : ‖B-A0‖ ≤ c/2) :
    ∃ a b : E3 ≃L[ℝ] E3, a.toContinuousLinearMap=A ∧ b.toContinuousLinearMap=B ∧
      ‖a.symm.toContinuousLinearMap‖ ≤ 2/c ∧ ‖b.symm.toContinuousLinearMap‖ ≤ 2/c ∧
      ‖a.symm.toContinuousLinearMap-b.symm.toContinuousLinearMap‖ ≤ (4/c^2)*‖A-B‖ :=
/- SWARM_PROOF_BEGIN -/
by
  have hAc : ∀ v : E3, (c / 2) * ‖v‖ ^ 2 ≤ inner ℝ (A v) v :=
    coercivity_survives_operator_perturbation A0 A c hc hA0 hA
  have hBc : ∀ v : E3, (c / 2) * ‖v‖ ^ 2 ≤ inner ℝ (B v) v :=
    coercivity_survives_operator_perturbation A0 B c hc hA0 hB
  have hc2 : 0 < c / 2 := by positivity
  obtain ⟨a, ha, ha_bound⟩ := coercive_operator_inverse A (c / 2) hc2 hAc
  obtain ⟨b, hb, hb_bound⟩ := coercive_operator_inverse B (c / 2) hc2 hBc
  have hc0 : c ≠ 0 := ne_of_gt hc
  have ha_bound' : ‖a.symm.toContinuousLinearMap‖ ≤ 2 / c := by
    calc
      ‖a.symm.toContinuousLinearMap‖ ≤ 1 / (c / 2) := ha_bound
      _ = 2 / c := by field_simp
  have hb_bound' : ‖b.symm.toContinuousLinearMap‖ ≤ 2 / c := by
    calc
      ‖b.symm.toContinuousLinearMap‖ ≤ 1 / (c / 2) := hb_bound
      _ = 2 / c := by field_simp
  refine ⟨a, b, ha, hb, ?_, ?_, ?_⟩
  · exact ha_bound'
  · exact hb_bound'
  · calc
      ‖a.symm.toContinuousLinearMap - b.symm.toContinuousLinearMap‖ ≤
          ‖a.symm.toContinuousLinearMap‖ *
            ‖a.toContinuousLinearMap - b.toContinuousLinearMap‖ *
              ‖b.symm.toContinuousLinearMap‖ :=
        inverse_operator_difference_bound a b
      _ ≤ (2 / c) * ‖a.toContinuousLinearMap - b.toContinuousLinearMap‖ * (2 / c) := by
        gcongr
      _ = (4 / c ^ 2) * ‖A - B‖ := by
        rw [ha, hb]
        field_simp
        ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
