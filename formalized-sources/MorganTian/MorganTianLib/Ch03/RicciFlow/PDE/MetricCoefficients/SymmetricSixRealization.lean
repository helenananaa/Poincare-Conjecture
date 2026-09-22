import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SixLinearAction
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SixActionBound
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
/-- Six actual independent coordinates for symmetric three-dimensional matrices. -/
def symmetricSixMatrix (q : E6) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q 0, q 3, q 4; q 3, q 1, q 5; q 4, q 5, q 2]
/-- A genuine injective continuous-linear encoding into metric coefficient operators. -/
theorem symmetric_six_realization :
    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖ ≤ 3 ∧
      (∀ (q : E6) (v : E3) (i : Fin 3), (E q v) i =
        ∑ j : Fin 3, symmetricSixMatrix q i j * v j) ∧
      (∀ (q : E6) (v w : E3), inner ℝ (E q v) w = inner ℝ v (E q w)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨E, hE_inj, hE_action⟩ := six_linear_action
  refine ⟨E, hE_inj, ?_, ?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound E (by positivity) ?_
    intro q
    refine ContinuousLinearMap.opNorm_le_bound (E q) (by positivity) ?_
    intro v
    have hEv : E q v = WithLp.toLp 2 (fun i : Fin 3 =>
        ∑ j : Fin 3, symmetricSixMatrix q i j * v j) := by
      ext i
      simpa [symmetricSixMatrix] using hE_action q v i
    rw [hEv]
    exact six_action_bound q v
  · intro q v i
    simpa [symmetricSixMatrix] using hE_action q v i
  · intro q v w
    simp only [PiLp.inner_apply, Real.inner_apply]
    simp_rw [hE_action]
    simp [Fin.sum_univ_succ]
    ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
