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
/-- The canonical inverse preserves metric symmetry and has actual positive quadratic bounds. -/
theorem symmetric_inverse_bounds (A : E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hsym : ∀ u v : E3, inner ℝ (A u) v = inner ℝ u (A v)) :
    (∀ u v : E3, inner ℝ (A.inverse u) v = inner ℝ u (A.inverse v)) ∧
    ∀ v : E3, (c/‖A‖^2)*‖v‖^2 ≤ inner ℝ (A.inverse v) v ∧
      inner ℝ (A.inverse v) v ≤ (1/c)*‖v‖^2 :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨e, he, he_bound⟩ := coercive_operator_inverse A c hc hA
  have hInv : ContinuousLinearMap.IsInvertible A := ⟨e, he⟩
  have hinv_bound : ‖A.inverse‖ ≤ 1 / c := by
    rw [← he]
    simpa using he_bound
  have hA_ne : A ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ := exists_ne (0 : E3)
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h := hA x
    simp [hzero] at h
    nlinarith [sq_pos_of_pos hxnorm]
  have hnormA : 0 < ‖A‖ := norm_pos_iff.mpr hA_ne
  constructor
  · intro u v
    have h := hsym (A.inverse u) (A.inverse v)
    simpa [hInv.self_apply_inverse] using h.symm
  · intro v
    have hnormv : ‖v‖ ≤ ‖A‖ * ‖A.inverse v‖ := by
      calc
        ‖v‖ = ‖A (A.inverse v)‖ := by rw [hInv.self_apply_inverse]
        _ ≤ ‖A‖ * ‖A.inverse v‖ := A.le_opNorm _
    have hsq : ‖v‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖A.inverse v‖ ^ 2 := by
      simpa [mul_pow] using
        ((sq_le_sq₀ (norm_nonneg v)
          (mul_nonneg (norm_nonneg A) (norm_nonneg (A.inverse v)))).2 hnormv)
    have hscale : (c / ‖A‖ ^ 2) * ‖v‖ ^ 2 ≤ c * ‖A.inverse v‖ ^ 2 := by
      calc
        (c / ‖A‖ ^ 2) * ‖v‖ ^ 2 ≤
            (c / ‖A‖ ^ 2) * (‖A‖ ^ 2 * ‖A.inverse v‖ ^ 2) := by
          gcongr
        _ = c * ‖A.inverse v‖ ^ 2 := by field_simp
    have hcoercive : c * ‖A.inverse v‖ ^ 2 ≤
        inner ℝ (A.inverse v) v := by
      calc
        c * ‖A.inverse v‖ ^ 2 ≤
            inner ℝ (A (A.inverse v)) (A.inverse v) := hA _
        _ = inner ℝ v (A.inverse v) := by rw [hInv.self_apply_inverse]
        _ = inner ℝ (A.inverse v) v := real_inner_comm _ _
    have hinv_v : ‖A.inverse v‖ ≤ (1 / c) * ‖v‖ := by
      calc
        ‖A.inverse v‖ ≤ ‖A.inverse‖ * ‖v‖ := A.inverse.le_opNorm _
        _ ≤ (1 / c) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hinv_bound (norm_nonneg _)
    constructor
    · exact hscale.trans hcoercive
    · calc
        inner ℝ (A.inverse v) v ≤ ‖A.inverse v‖ * ‖v‖ :=
          real_inner_le_norm _ _
        _ ≤ ((1 / c) * ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hinv_v (norm_nonneg _)
        _ = (1 / c) * ‖v‖ ^ 2 := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
