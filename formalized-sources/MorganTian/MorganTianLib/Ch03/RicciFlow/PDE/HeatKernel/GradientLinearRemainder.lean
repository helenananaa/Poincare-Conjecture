import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set Function Filter
open scoped ContDiff Topology
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Differentiability of the real gradient gives its uniform first-order remainder. -/
theorem gradient_local_linear_remainder (f : E3 → ℝ) (hf : ContDiff ℝ 2 f) (x : E3) :
    ∀ eta : ℝ, 0<eta → ∃ r : ℝ, 0<r ∧ ∀ z : E3, ‖z-x‖<r →
      ‖fderiv ℝ f z-fderiv ℝ f x-(fderiv ℝ (fderiv ℝ f) x) (z-x)‖ ≤ eta*‖z-x‖ :=
/- SWARM_PROOF_BEGIN -/
by
  intro eta heta
  have hcont : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    hf.contDiffAt.fderiv_right (m := 1) (by norm_num)
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    hcont.differentiableAt_one.hasFDerivAt
  have hrem := hfd.isLittleO.bound heta
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hrem
  refine ⟨r, hr, ?_⟩
  intro z hz
  exact hball z hz
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
