import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function
open scoped Topology RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Exact inverse-difference control for actual continuous linear equivalences. -/
theorem inverse_operator_difference_bound (a b : E3 ≃L[ℝ] E3) :
    ‖a.symm.toContinuousLinearMap-b.symm.toContinuousLinearMap‖ ≤
      ‖a.symm.toContinuousLinearMap‖*‖a.toContinuousLinearMap-b.toContinuousLinearMap‖*
        ‖b.symm.toContinuousLinearMap‖ :=
/- SWARM_PROOF_BEGIN -/
by
  have hresolvent :
      a.symm.toContinuousLinearMap - b.symm.toContinuousLinearMap =
        (a.symm.toContinuousLinearMap ∘L
          (b.toContinuousLinearMap - a.toContinuousLinearMap)) ∘L
            b.symm.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      map_sub, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [hresolvent]
  have hnorm :
      ‖b.toContinuousLinearMap - a.toContinuousLinearMap‖ =
        ‖a.toContinuousLinearMap - b.toContinuousLinearMap‖ := by
    rw [← norm_neg]
    congr 1
    abel
  calc
    ‖(a.symm.toContinuousLinearMap ∘L
        (b.toContinuousLinearMap - a.toContinuousLinearMap)) ∘L
          b.symm.toContinuousLinearMap‖ ≤
        ‖a.symm.toContinuousLinearMap ∘L
          (b.toContinuousLinearMap - a.toContinuousLinearMap)‖ *
          ‖b.symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖a.symm.toContinuousLinearMap‖ *
        ‖b.toContinuousLinearMap - a.toContinuousLinearMap‖) *
          ‖b.symm.toContinuousLinearMap‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖a.symm.toContinuousLinearMap‖ *
        ‖a.toContinuousLinearMap - b.toContinuousLinearMap‖ *
          ‖b.symm.toContinuousLinearMap‖ := by rw [hnorm]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
