import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixMetricTimeDerivative
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
theorem six_metric_time_derivative
    (u : ℝ → E6) (du : E6) (t : ℝ) (hu : HasDerivAt u du t) :

    ∀ i j : Idx, HasDerivAt (fun s : ℝ => (if i=j then 1 else 0)+symmetricSixMatrix (u s) i j)
      (symmetricSixMatrix du i j) t :=
/- SWARM_PROOF_BEGIN -/
by
  intro i j
  have hcoord (k : Fin 6) :
      HasDerivAt (fun s : ℝ => (u s) k) (du k) t := by
    have heval := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (E := fun _ : Fin 6 => ℝ)
      (p := 2) (f := u t) k
    have h := heval.comp_hasDerivAt_of_eq t hu (by simp)
    simpa [Function.comp_def, PiLp.proj] using h
  have hmetric : HasDerivAt (fun s : ℝ => symmetricSixMatrix (u s) i j)
      (symmetricSixMatrix du i j) t := by
    fin_cases i <;> fin_cases j <;>
    first
    | simpa [symmetricSixMatrix] using hcoord 0
    | simpa [symmetricSixMatrix] using hcoord 1
    | simpa [symmetricSixMatrix] using hcoord 2
    | simpa [symmetricSixMatrix] using hcoord 3
    | simpa [symmetricSixMatrix] using hcoord 4
    | simpa [symmetricSixMatrix] using hcoord 5
  exact hmetric.const_add (if i=j then 1 else 0)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixMetricTimeDerivative
