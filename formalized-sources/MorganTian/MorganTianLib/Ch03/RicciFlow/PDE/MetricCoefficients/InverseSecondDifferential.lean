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
/-- The actual second derivative of inversion, with noncommutative factor order. -/
theorem coercive_inverse_second_differential (A : E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0<c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (H K : E3 →L[ℝ] E3) :
    fderiv ℝ (fun B : E3 →L[ℝ] E3 =>
      fderiv ℝ (fun C : E3 →L[ℝ] E3 => C.inverse) B H) A K =
      A.inverse.comp (K.comp (A.inverse.comp (H.comp A.inverse))) +
      A.inverse.comp (H.comp (A.inverse.comp (K.comp A.inverse))) :=
/- SWARM_PROOF_BEGIN -/
by
  have hAinv : DifferentiableAt ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) A :=
    (coercive_inverse_differential A c hc hA).1.differentiableAt (by simp)
  have hlocal :
      (fun B : E3 →L[ℝ] E3 =>
        fderiv ℝ (fun C : E3 →L[ℝ] E3 => C.inverse) B H) =ᶠ[nhds A]
      (fun B : E3 →L[ℝ] E3 =>
        -(B.inverse.comp (H.comp B.inverse))) := by
    filter_upwards [Metric.ball_mem_nhds A (show 0 < c / 2 by positivity)] with B hB
    have hBA : ‖B - A‖ ≤ c / 2 := by
      have hdist : dist B A < c / 2 := hB
      simpa [dist_eq_norm] using (le_of_lt hdist)
    have hBc : ∀ v : E3, (c / 2) * ‖v‖ ^ 2 ≤ inner ℝ (B v) v :=
      coercivity_survives_operator_perturbation A B c hc hA hBA
    exact (coercive_inverse_differential B (c / 2) (by positivity) hBc).2 H
  rw [Filter.EventuallyEq.fderiv_eq hlocal]
  have hneg :
      fderiv ℝ (fun B : E3 →L[ℝ] E3 =>
        -(B.inverse.comp (H.comp B.inverse))) A =
      -fderiv ℝ (fun B : E3 →L[ℝ] E3 =>
        B.inverse.comp (H.comp B.inverse)) A := by
    rw [show (fun B : E3 →L[ℝ] E3 =>
        -(B.inverse.comp (H.comp B.inverse))) =
        -(fun B : E3 →L[ℝ] E3 => B.inverse.comp (H.comp B.inverse)) by
      funext B
      rfl]
    exact fderiv_neg
  rw [hneg]
  have hHconst : DifferentiableAt ℝ (fun _ : E3 →L[ℝ] E3 => H) A :=
    differentiableAt_const H
  have hH : DifferentiableAt ℝ (fun B : E3 →L[ℝ] E3 => H.comp B.inverse) A :=
    hHconst.clm_comp hAinv
  rw [fderiv_clm_comp hAinv hH]
  rw [fderiv_clm_comp hHconst hAinv]
  have hfd :
      fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) A =
        -((ContinuousLinearMap.compL ℝ E3 E3 E3 A.inverse).comp
          ((ContinuousLinearMap.compL ℝ E3 E3 E3).flip A.inverse)) := by
    apply ContinuousLinearMap.ext
    intro L
    simpa [ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply] using
      (coercive_inverse_differential A c hc hA |>.2 L)
  have hconstfd :
      fderiv ℝ (fun _ : E3 →L[ℝ] E3 => H) A = 0 := by
    simpa [Function.const] using
      congrFun (fderiv_const (𝕜 := ℝ) H) A
  rw [hfd, hconstfd]
  simp only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.comp_apply]
  ext v
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
