import Mathlib
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ

/-- **Math.** metric germ first second jets. -/
theorem metric_germ_first_second_jets (G H : E3 → (E3 →L[ℝ] E3)) (x : E3) (h : G =ᶠ[𝓝 x] H) :
    G x = H x ∧ fderiv ℝ G x = fderiv ℝ H x ∧
      ∀ v : E3, fderiv ℝ (fun y : E3 => fderiv ℝ G y v) x =
        fderiv ℝ (fun y : E3 => fderiv ℝ H y v) x :=
/- SWARM_PROOF_BEGIN -/
by
  refine ⟨h.eq_of_nhds, h.fderiv_eq, ?_⟩
  intro v
  have hv : (fun y : E3 => fderiv ℝ G y v) =ᶠ[𝓝 x]
      (fun y : E3 => fderiv ℝ H y v) :=
    h.fderiv.mono fun y hy => congrArg (fun A : E3 →L[ℝ] (E3 →L[ℝ] E3) => A v) hy
  exact hv.fderiv.eq_of_nhds
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
