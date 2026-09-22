import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Smooth inversion and its actual derivative at a coercive metric coefficient. -/
theorem coercive_inverse_differential (A : E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) :
    ContDiffAt ℝ ∞ (fun B : E3 →L[ℝ] E3 => B.inverse) A ∧
    ∀ H : E3 →L[ℝ] E3,
      fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) A H =
        -(A.inverse.comp (H.comp A.inverse)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨e, he, _⟩ := coercive_operator_inverse A c hc hA
  constructor
  · rw [← he]
    exact contDiffAt_map_inverse e
  intro H
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) e.toUnit).fderiv
  rw [ContinuousLinearMap.ringInverse_eq_inverse] at h
  have hv : (e.toUnit : E3 →L[ℝ] E3) = A := he
  rw [hv] at h
  rw [h]
  have hinv : ((e.toUnit⁻¹ : (E3 →L[ℝ] E3)ˣ) : E3 →L[ℝ] E3) = A.inverse := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
    rfl
  rw [hinv]
  ext v
  simp [ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.comp_apply]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
