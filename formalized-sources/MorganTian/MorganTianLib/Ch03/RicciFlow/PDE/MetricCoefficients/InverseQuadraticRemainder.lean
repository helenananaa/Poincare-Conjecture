import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- A genuine second-order remainder for inverse metric coefficients. -/
theorem coercive_inverse_quadratic_remainder (A H : E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0<c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hH : ‖H‖ ≤ c/2) :
    ‖(A+H).inverse-A.inverse+A.inverse.comp (H.comp A.inverse)‖ ≤
      (2/c^3)*‖H‖^2 :=
/- SWARM_PROOF_BEGIN -/
by
  have hAH : ∀ v : E3, (c / 2) * ‖v‖ ^ 2 ≤ inner ℝ ((A + H) v) v := by
    apply coercivity_survives_operator_perturbation A (A + H) c hc hA
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hH
  have hc2 : 0 < c / 2 := by positivity
  obtain ⟨a, ha, ha_bound⟩ := coercive_operator_inverse A c hc hA
  obtain ⟨b, hb, hb_bound⟩ := coercive_operator_inverse (A + H) (c / 2) hc2 hAH
  have hAinv : ContinuousLinearMap.IsInvertible A := ⟨a, ha⟩
  have hAHinv : ContinuousLinearMap.IsInvertible (A + H) := ⟨b, hb⟩
  have hA_bound : ‖A.inverse‖ ≤ 1 / c := by
    rw [← ha]
    simpa using ha_bound
  have hAH_bound : ‖(A + H).inverse‖ ≤ 2 / c := by
    rw [← hb]
    rw [ContinuousLinearMap.inverse_equiv]
    calc
      ‖b.symm.toContinuousLinearMap‖ ≤ 1 / (c / 2) := hb_bound
      _ = 2 / c := by field_simp
  have hresolvent :
      A.inverse = (A + H).inverse +
        A.inverse.comp (H.comp (A + H).inverse) := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      A.inverse x = A.inverse ((A + H) ((A + H).inverse x)) := by
        rw [hAHinv.self_apply_inverse]
      _ = A.inverse (A ((A + H).inverse x)) +
          A.inverse (H ((A + H).inverse x)) := by
        simp only [map_add, add_apply]
      _ = (A + H).inverse x + A.inverse (H ((A + H).inverse x)) := by
        rw [hAinv.inverse_apply_self]
      _ = ((A + H).inverse +
          A.inverse.comp (H.comp (A + H).inverse)) x := by
        simp only [add_apply, ContinuousLinearMap.comp_apply]
  have hquadratic :
      (A + H).inverse - A.inverse + A.inverse.comp (H.comp A.inverse) =
        A.inverse.comp (H.comp (A.inverse.comp (H.comp (A + H).inverse))) := by
    have hdiff :
        (A + H).inverse - A.inverse =
          -(A.inverse.comp (H.comp (A + H).inverse)) := by
      calc
        (A + H).inverse - A.inverse =
            (A + H).inverse -
              ((A + H).inverse + A.inverse.comp (H.comp (A + H).inverse)) :=
          congrArg (fun T => (A + H).inverse - T) hresolvent
        _ = -(A.inverse.comp (H.comp (A + H).inverse)) := by abel
    have hterm :
        A.inverse.comp (H.comp A.inverse) =
          A.inverse.comp (H.comp (A + H).inverse) +
            A.inverse.comp
              (H.comp (A.inverse.comp (H.comp (A + H).inverse))) := by
      calc
        A.inverse.comp (H.comp A.inverse) =
            A.inverse.comp
              (H.comp ((A + H).inverse +
                A.inverse.comp (H.comp (A + H).inverse))) :=
          congrArg (fun T => A.inverse.comp (H.comp T)) hresolvent
        _ = A.inverse.comp (H.comp (A + H).inverse) +
            A.inverse.comp
              (H.comp (A.inverse.comp (H.comp (A + H).inverse))) := by
          apply ContinuousLinearMap.ext
          intro x
          simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]
    calc
      (A + H).inverse - A.inverse + A.inverse.comp (H.comp A.inverse) =
          -(A.inverse.comp (H.comp (A + H).inverse)) +
            (A.inverse.comp (H.comp (A + H).inverse) +
              A.inverse.comp
                (H.comp (A.inverse.comp (H.comp (A + H).inverse)))) := by
        rw [hdiff, hterm]
      _ = A.inverse.comp
          (H.comp (A.inverse.comp (H.comp (A + H).inverse))) := by abel
  rw [hquadratic]
  calc
    ‖A.inverse.comp (H.comp (A.inverse.comp (H.comp (A + H).inverse)))‖ ≤
        ‖A.inverse‖ * ‖H‖ * ‖A.inverse‖ * ‖H‖ * ‖(A + H).inverse‖ := by
      calc
        _ ≤ ‖A.inverse‖ *
            ‖H.comp (A.inverse.comp (H.comp (A + H).inverse))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖A.inverse‖ * (‖H‖ *
            ‖A.inverse.comp (H.comp (A + H).inverse)‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖A.inverse‖ * (‖H‖ *
            (‖A.inverse‖ * ‖H.comp (A + H).inverse‖)) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖A.inverse‖ * (‖H‖ *
            (‖A.inverse‖ * (‖H‖ * ‖(A + H).inverse‖))) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖A.inverse‖ * ‖H‖ * ‖A.inverse‖ * ‖H‖ * ‖(A + H).inverse‖ := by ring
    _ ≤ (1 / c) * ‖H‖ * (1 / c) * ‖H‖ * (2 / c) := by
      gcongr
    _ = (2 / c ^ 3) * ‖H‖ ^ 2 := by
      field_simp
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
