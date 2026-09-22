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
  have hfun :
      (fun B : E3 →L[ℝ] E3 => B.inverse) =
        (fun B : E3 →L[ℝ] E3 =>
          Ring.inverse ((e.symm : E3 →L[ℝ] E3).comp B) ∘L
            (e.symm : E3 →L[ℝ] E3)) := by
    funext B
    exact ContinuousLinearMap.inverse_eq_ringInverse e B
  rw [hfun]
  have hleft :
      HasFDerivAt
        (fun B : E3 →L[ℝ] E3 => (e.symm : E3 →L[ℝ] E3).comp B)
        (ContinuousLinearMap.compL ℝ E3 E3 E3 (e.symm : E3 →L[ℝ] E3)) A := by
    simpa using
      (hasFDerivAt_const (e.symm : E3 →L[ℝ] E3) A).clm_comp
        (hasFDerivAt_id A)
  have hmid :
      HasFDerivAt
        (fun B : E3 →L[ℝ] E3 =>
          Ring.inverse ((e.symm : E3 →L[ℝ] E3).comp B))
        ((-ContinuousLinearMap.mulLeftRight ℝ (E3 →L[ℝ] E3)
            (↑(1 : (E3 →L[ℝ] E3)ˣ)⁻¹) (↑(1 : (E3 →L[ℝ] E3)ˣ)⁻¹)).comp
          (ContinuousLinearMap.compL ℝ E3 E3 E3 (e.symm : E3 →L[ℝ] E3))) A := by
    have hbase :
        (e.symm : E3 →L[ℝ] E3).comp A =
          (1 : E3 →L[ℝ] E3) := by
      rw [← he]
      ext v
      simp
    have hring :
        HasFDerivAt Ring.inverse
          (-ContinuousLinearMap.mulLeftRight ℝ (E3 →L[ℝ] E3)
            (↑(1 : (E3 →L[ℝ] E3)ˣ)⁻¹) (↑(1 : (E3 →L[ℝ] E3)ˣ)⁻¹))
          ((e.symm : E3 →L[ℝ] E3).comp A) := by
      simpa [hbase] using
        (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (E3 →L[ℝ] E3)ˣ))
    have hring' := hring.comp A hleft
    simpa [Function.comp_def] using hring'
  have hright :
      HasFDerivAt
        (fun D : E3 →L[ℝ] E3 => D.comp (e.symm : E3 →L[ℝ] E3))
        ((ContinuousLinearMap.compL ℝ E3 E3 E3).flip
          (e.symm : E3 →L[ℝ] E3))
        (Ring.inverse ((e.symm : E3 →L[ℝ] E3).comp A)) := by
    have hbase :
        (e.symm : E3 →L[ℝ] E3).comp A =
          (1 : E3 →L[ℝ] E3) := by
      rw [← he]
      ext v
      simp
    simpa [hbase] using
      (hasFDerivAt_id (Ring.inverse ((e.symm : E3 →L[ℝ] E3).comp A))).clm_comp
        (hasFDerivAt_const (e.symm : E3 →L[ℝ] E3)
          (Ring.inverse ((e.symm : E3 →L[ℝ] E3).comp A)))
  have htotal := hright.comp A hmid
  have hderiv := htotal.fderiv
  have hderiv' :
      fderiv ℝ
          (fun B : E3 →L[ℝ] E3 =>
            Ring.inverse ((e.symm : E3 →L[ℝ] E3).comp B) ∘L
              (e.symm : E3 →L[ℝ] E3)) A =
        (ContinuousLinearMap.compL ℝ E3 E3 E3).flip
            (e.symm : E3 →L[ℝ] E3) ∘L
          ((-ContinuousLinearMap.mulLeftRight ℝ (E3 →L[ℝ] E3)
              (↑(1 : (E3 →L[ℝ] E3)ˣ)⁻¹) (↑(1 : (E3 →L[ℝ] E3)ˣ)⁻¹)).comp
            (ContinuousLinearMap.compL ℝ E3 E3 E3 (e.symm : E3 →L[ℝ] E3))) := by
    simpa [Function.comp_def] using hderiv
  rw [hderiv']
  rw [← he, ContinuousLinearMap.inverse_equiv]
  ext K
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_assoc]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
