import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.Basic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ScalarCoordinateLineDerivative
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem fderiv_eq_coordinate_deriv
    (f : E3 → ℝ) (x : E3) (a : Idx) (hf : DifferentiableAt ℝ f x) :

    fderiv ℝ f x (EuclideanSpace.single a 1) =
      deriv (fun t : ℝ => f (x + t • EuclideanSpace.single a 1)) 0 :=
/- SWARM_PROOF_BEGIN -/
by
  let v : E3 := EuclideanSpace.single a 1
  have hline : HasFDerivAt (fun t : ℝ => x + t • v)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v) 0 := by
    simpa using ((hasFDerivAt_id 0).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  have hcomp := HasFDerivAt.comp (f := fun t : ℝ => x + t • v)
    (x := (0 : ℝ)) hf' hline
  have hderiv : HasDerivAt (fun t : ℝ => f (x + t • v))
      ((fderiv ℝ f x) v) 0 := by
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using hcomp.hasDerivAt
  exact hderiv.deriv.symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ScalarCoordinateLineDerivative
