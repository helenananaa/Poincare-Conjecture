import PoincareConjecture.ProofContract.Refinement20260927.RegularizedTransferRoot
import PoincareConjecture.ParallelImplementation.RefinedIntrinsicMetricComparison
import PoincareConjecture.ParallelImplementation.RefinedRelativeRetractionHomotopy
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
/-- **Math.** Exact returned target, independently recompiled from source. -/
theorem checked_intrinsic_metric_comparison : IntrinsicMetricTimeComparisonStatement.{u} :=
  ParallelImplementation.RefinedIntrinsicMetricComparison.intrinsic_metric_comparison
/-- **Math.** Exact relative homotopy target, with the given retraction. -/
theorem checked_relative_retraction : RelativeRetractionHomotopyStatement.{u} :=
  ParallelImplementation.RefinedRelativeRetractionHomotopy.relative_retraction_homotopy
/-- **Math.** Energy approximation and three large research inputs remain. -/
theorem public_after_twentyFour (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (energy : SphereEnergyApproximationStatement.{u})
    (geometry : RegularizedIntrinsicGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_of_regularization_frontier triangulate atlas checked_intrinsic_metric_comparison
    checked_relative_retraction energy geometry
#print axioms checked_intrinsic_metric_comparison
#print axioms checked_relative_retraction
#print axioms public_after_twentyFour
end PoincareConjecture.ProofContract.Refinement20260927
