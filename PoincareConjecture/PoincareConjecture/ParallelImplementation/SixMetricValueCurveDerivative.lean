import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixMetricValueCurveDerivative
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem six_value_curve_derivative
    (u : E3 → E6) (A : E3 →L[ℝ] E6) (x : E3) (hu : HasFDerivAt u A x) :

    ∀ a i j : Idx, HasDerivAt
      (fun t : ℝ => symmetricSixMatrix (u (x + t • EuclideanSpace.single a 1)) i j)
      (symmetricSixMatrix (A (EuclideanSpace.single a 1)) i j) 0 :=
/- SWARM_PROOF_BEGIN -/
by
  intro a i j
  let v : E3 := EuclideanSpace.single a 1
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa [v] using (hasDerivAt_id' (0 : ℝ)).smul_const v |>.const_add x
  have hu' : HasDerivAt (fun t : ℝ => u (x + t • v)) (A v) 0 := by
    have hcomp := hu.comp_hasDerivAt_of_eq 0 hline (by simp)
    simpa only [Function.comp_def] using hcomp
  have hcoord (k : Fin 6) :
      HasDerivAt (fun t : ℝ => (u (x + t • v)) k) ((A v) k) 0 := by
    have heval := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (E := fun _ : Fin 6 => ℝ)
      (p := 2) (f := u x) k
    have h := heval.comp_hasDerivAt_of_eq 0 hu' (by simp)
    simpa [Function.comp_def, PiLp.proj] using h
  fin_cases i <;> fin_cases j <;>
    first
    | simpa [symmetricSixMatrix, v] using hcoord 0
    | simpa [symmetricSixMatrix, v] using hcoord 1
    | simpa [symmetricSixMatrix, v] using hcoord 2
    | simpa [symmetricSixMatrix, v] using hcoord 3
    | simpa [symmetricSixMatrix, v] using hcoord 4
    | simpa [symmetricSixMatrix, v] using hcoord 5
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixMetricValueCurveDerivative
