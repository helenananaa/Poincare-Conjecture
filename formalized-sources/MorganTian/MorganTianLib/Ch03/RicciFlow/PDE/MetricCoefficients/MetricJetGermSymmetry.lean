import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricJetSymmetry
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** metric jet selfadjoint of eventually. -/
theorem metric_jet_selfadjoint_of_eventually (G : E3 → (E3 →L[ℝ] E3)) (x : E3) (hG : DifferentiableAt ℝ G x)
    (hsym : ∀ᶠ y : E3 in 𝓝 x, ∀ v w : E3, inner ℝ (G y v) w = inner ℝ v (G y w)) :
    ∀ h v w : E3, inner ℝ (fderiv ℝ G x h v) w = inner ℝ v (fderiv ℝ G x h w) :=
/- SWARM_PROOF_BEGIN -/
by
  intro h v w
  have hGv : DifferentiableAt ℝ (fun y : E3 => G y v) x :=
    hG.clm_apply (differentiableAt_const (c := v) (x := x))
  have hGw : DifferentiableAt ℝ (fun y : E3 => G y w) x :=
    hG.clm_apply (differentiableAt_const (c := w) (x := x))
  have hGv' : fderiv ℝ (fun y : E3 => G y v) x h = (fderiv ℝ G x h) v := by
    have h' := fderiv_clm_apply hG (differentiableAt_const (c := v) (x := x))
    simpa using congrArg (fun L => L h) h'
  have hGw' : fderiv ℝ (fun y : E3 => G y w) x h = (fderiv ℝ G x h) w := by
    have h' := fderiv_clm_apply hG (differentiableAt_const (c := w) (x := x))
    simpa using congrArg (fun L => L h) h'
  have hleft := fderiv_inner_apply ℝ hGv
    (differentiableAt_const (c := w) (x := x)) h
  have hright := fderiv_inner_apply ℝ
    (differentiableAt_const (c := v) (x := x)) hGw h
  have hEq : (fun y : E3 => inner ℝ (G y v) w) =ᶠ[𝓝 x]
      (fun y : E3 => inner ℝ v (G y w)) := by
    filter_upwards [hsym] with y hy
    exact hy v w
  have hder : fderiv ℝ (fun y : E3 => inner ℝ (G y v) w) x =
      fderiv ℝ (fun y : E3 => inner ℝ v (G y w)) x :=
    Filter.EventuallyEq.fderiv_eq hEq
  calc
    inner ℝ ((fderiv ℝ G x h) v) w =
        fderiv ℝ (fun y : E3 => inner ℝ (G y v) w) x h := by
          simpa [hGv'] using hleft.symm
    _ = fderiv ℝ (fun y : E3 => inner ℝ v (G y w)) x h := by rw [hder]
    _ = inner ℝ v ((fderiv ℝ G x h) w) := by
          simpa [hGw'] using hright
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
