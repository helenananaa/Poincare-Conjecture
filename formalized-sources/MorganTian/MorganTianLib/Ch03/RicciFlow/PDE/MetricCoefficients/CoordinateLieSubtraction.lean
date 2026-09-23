import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateLieMetricLowering
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** coordinate lie subtraction. -/
theorem coordinate_lie_subtraction (G : E3 → (E3 →L[ℝ] E3)) (W Z : E3 → E3) (x : E3)
    (hW : DifferentiableAt ℝ W x) (hZ : DifferentiableAt ℝ Z x) (i j : Fin 3) :
    coordinateLieMetricExpr G (fun y => W y-Z y) x i j =
      coordinateLieMetricExpr G W x i j - coordinateLieMetricExpr G Z x i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hsub : fderiv ℝ (fun y : E3 => W y - Z y) x =
      fderiv ℝ W x - fderiv ℝ Z x := fderiv_sub hW hZ
  have hsum (a u v : Fin 3 → ℝ) :
      (∑ k : Fin 3, (a k * u k - a k * v k)) =
        (∑ k : Fin 3, a k * u k) - (∑ k : Fin 3, a k * v k) := by
    rw [← Finset.sum_sub_distrib]
  dsimp [coordinateLieMetricExpr]
  rw [hsub]
  simp only [sub_apply, map_sub, WithLp.ofLp_sub, Pi.sub_apply, mul_sub,
    Finset.sum_add_distrib]
  rw [hsum (fun k => (G x (EuclideanSpace.single k 1)).ofLp j)
      (fun k => (fderiv ℝ W x (EuclideanSpace.single i 1)).ofLp k)
      (fun k => (fderiv ℝ Z x (EuclideanSpace.single i 1)).ofLp k),
    hsum (fun k => (G x (EuclideanSpace.single k 1)).ofLp i)
      (fun k => (fderiv ℝ W x (EuclideanSpace.single j 1)).ofLp k)
      (fun k => (fderiv ℝ Z x (EuclideanSpace.single j 1)).ofLp k)]
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
