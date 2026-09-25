import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixMetricOperatorRealization
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
theorem metric_operator_realization
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j * v j)
    (u : E3 → E6) (hu : ContDiff ℝ 2 u) :

    ContDiff ℝ 2 (metricOp E u) ∧ ∀ x : E3,
      (∀ i j : Idx, (metricOp E u x (EuclideanSpace.single j 1)) i = metricCoefficients u x i j) ∧
      HasFDerivAt (metricOp E u) (E.comp (fderiv ℝ u x)) x :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · unfold metricOp
    exact contDiff_const.add (E.contDiff.comp hu)
  · intro x
    constructor
    · intro i j
      simp [metricOp, metricCoefficients, hE]
    · have hcomp : HasFDerivAt (fun y : E3 => E (u y))
          (E.comp (fderiv ℝ u x)) x :=
        E.hasFDerivAt.comp x ((hu.differentiable (by norm_num) x).hasFDerivAt)
      change HasFDerivAt (fun y : E3 => (1 : E3 →L[ℝ] E3) + E (u y)) _ x
      exact (hasFDerivAt_const_add_iff (1 : E3 →L[ℝ] E3)).2 hcomp
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixMetricOperatorRealization
