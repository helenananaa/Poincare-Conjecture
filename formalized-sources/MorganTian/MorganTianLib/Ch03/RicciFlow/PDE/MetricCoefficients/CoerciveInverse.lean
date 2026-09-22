import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function
open scoped Topology RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Coercivity produces an actual linear inverse with an explicit operator-norm bound. -/
theorem coercive_operator_inverse (A : E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) :
    ∃ e : E3 ≃L[ℝ] E3, e.toContinuousLinearMap=A ∧ ‖e.symm.toContinuousLinearMap‖ ≤ 1/c :=
/- SWARM_PROOF_BEGIN -/
by
  have hbound : ∀ v : E3, c * ‖v‖ ≤ ‖A v‖ := by
    intro v
    by_cases hv : 0 < ‖v‖
    · refine (mul_le_mul_iff_left₀ hv).mp ?_
      calc
        c * ‖v‖ * ‖v‖ ≤ inner ℝ (A v) v := by simpa [pow_two, mul_assoc] using hA v
        _ ≤ ‖A v‖ * ‖v‖ := real_inner_le_norm _ _
    · have hv0 : v = 0 := by simpa using hv
      simp [hv0]
  have hinj : Function.Injective (A : E3 →ₗ[ℝ] E3) := by
    intro u v huv
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have h := hbound (u - v)
    have hzero : A (u - v) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr huv
    rw [hzero, norm_zero] at h
    nlinarith [norm_nonneg (u - v)]
  have hsurj : Function.Surjective (A : E3 →ₗ[ℝ] E3) :=
    (LinearMap.injective_iff_surjective.mp hinj)
  let e : E3 ≃L[ℝ] E3 :=
    (LinearEquiv.ofBijective (A : E3 →ₗ[ℝ] E3) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have he : (e : E3 →L[ℝ] E3) = A := by
    ext v
    rfl
  refine ⟨e, he, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro w
  have h := hbound (e.symm w)
  rw [← he] at h
  have h' : c * ‖e.symm.toContinuousLinearMap w‖ ≤ ‖w‖ := by
    simpa using h
  have h'' : ‖e.symm.toContinuousLinearMap w‖ ≤ ‖w‖ / c :=
    (le_div_iff₀ hc).2 (by simpa [mul_comm] using h')
  simpa [one_div, div_eq_mul_inv, mul_comm] using h''
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
