import PoincareConjecture.ParallelImplementation.TimeDependentFlowJacobian
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FlowPullbackCoefficientDerivative
open Set
open scoped ContDiff Topology
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E3 →L[ℝ] E3 →L[ℝ] ℝ
local instance : NormedAddCommGroup (E3 →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E3 →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup Bilin := inferInstance
local instance : NormedSpace ℝ Bilin := inferInstance
/-- Differentiate actual pullback metric coefficients along an ODE flow.
Both Jacobian variation terms are derived rather than assumed. -/
theorem hasDerivAt_pullback_bilinear_coefficients
    (F V : ℝ × E3 → E3) (g : ℝ × E3 → Bilin)
    (J : Set ℝ) (U : Set E3) (hJ : IsOpen J) (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 F (J ×ˢ U))
    (hV : ContDiff ℝ 1 V) (hg : ContDiff ℝ 1 g)
    (hODE : ∀ t ∈ J, ∀ x ∈ U,
      HasDerivAt (fun s : ℝ => F (s,x)) (V (t,F (t,x))) t) :
    ∀ t ∈ J, ∀ x ∈ U, ∀ v w : E3,
      let A := fderiv ℝ (fun y : E3 => F (t,y)) x
      let B := fderiv ℝ (fun y : E3 => V (t,y)) (F (t,x))
      HasDerivAt (fun s : ℝ => g (s,F (s,x))
        (fderiv ℝ (fun y : E3 => F (s,y)) x v)
        (fderiv ℝ (fun y : E3 => F (s,y)) x w))
        ((fderiv ℝ g (t,F (t,x)) (1,V (t,F (t,x)))) (A v) (A w) +
          g (t,F (t,x)) (B (A v)) (A w) +
          g (t,F (t,x)) (A v) (B (A w))) t :=
/- SWARM_PROOF_BEGIN -/
by
  intro t ht x hx v w
  let A : E3 →L[ℝ] E3 := fderiv ℝ (fun y : E3 => F (t, y)) x
  let B : E3 →L[ℝ] E3 := fderiv ℝ (fun y : E3 => V (t, y)) (F (t, x))
  have hFcurve : HasDerivAt (fun s : ℝ => F (s, x)) (V (t, F (t, x))) t :=
    hODE t ht x hx
  have hpath : HasDerivAt (fun s : ℝ => (s, F (s, x)))
      (1, V (t, F (t, x))) t := by
    simpa using (hasDerivAt_id t).prodMk hFcurve
  have hgAt : ContDiffAt ℝ 1 g (t, F (t, x)) :=
    hg.contDiffAt (x := (t, F (t, x)))
  have hgHas : HasFDerivAt g (fderiv ℝ g (t, F (t, x))) (t, F (t, x)) :=
    (hgAt.differentiableAt (by norm_num)).hasFDerivAt
  have hgcurve : HasDerivAt (fun s : ℝ => g (s, F (s, x)))
      (fderiv ℝ g (t, F (t, x)) (1, V (t, F (t, x)))) t := by
    simpa [Function.comp_def] using hgHas.comp_hasDerivAt t hpath

  have hJac :=
    _root_.PoincareConjecture.ParallelImplementation.TimeDependentFlowJacobian.hasDerivAt_spatial_jacobian_of_flow_ode
      F V J U hJ hU hF hV hODE t ht x hx
  have hp : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun y : E3 => F (s, y)) x v)
      (B (A v)) t := by
    have h := HasDerivAt.clm_apply (𝕜 := ℝ) hJac
      (hasDerivAt_const (c := v) (x := t))
    simpa [A, B, ContinuousLinearMap.comp_apply] using h
  have hq : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun y : E3 => F (s, y)) x w)
      (B (A w)) t := by
    have h := HasDerivAt.clm_apply (𝕜 := ℝ) hJac
      (hasDerivAt_const (c := w) (x := t))
    simpa [A, B, ContinuousLinearMap.comp_apply] using h

  have hfirst := HasDerivAt.clm_apply (𝕜 := ℝ) hgcurve hp
  have hsecond := HasDerivAt.clm_apply (𝕜 := ℝ) hfirst hq
  apply hsecond.congr_deriv
  dsimp [A, B]
  rw [ContinuousLinearMap.add_apply]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FlowPullbackCoefficientDerivative
