import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckNonlinearityLocalControl
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
def fullDeTurckNonlinearity (q : J3) : E9 :=
  WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 =>
    -2*ricciLowerOrder q.1 q.2 ij.1 ij.2 + deturckLieLowerOrder q.1 q.2 ij.1 ij.2)

/-- **Math.** full deturck nonlinearity smooth. -/
theorem full_deturck_nonlinearity_smooth (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0 < c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) :
    ContDiffAt ℝ ∞ fullDeTurckNonlinearity (A,P) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : NormedAddCommGroup E9 := inferInstance
  letI : InnerProductSpace ℝ E9 := inferInstance
  apply contDiffAt_euclidean.mpr
  intro ij
  change ContDiffAt ℝ ∞
    (fun q : J3 =>
      -2 * ricciLowerOrder q.1 q.2 ij.1 ij.2 +
        deturckLieLowerOrder q.1 q.2 ij.1 ij.2) (A, P)
  exact (deturck_nonlinearity_local_control A P c hc hA ij.1 ij.2).1
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
