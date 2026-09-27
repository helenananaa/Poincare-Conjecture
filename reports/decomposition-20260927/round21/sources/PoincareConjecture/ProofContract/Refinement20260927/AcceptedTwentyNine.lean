import PoincareConjecture.ProofContract.Refinement20260927.NormalTubeRoot
import PoincareConjecture.ParallelImplementation.RefinedNormalLinearEquiv
import PoincareConjecture.ParallelImplementation.RefinedNormalEndpointJet
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
/-- **Math.** Exact audited proof of the normal tangent/complement splitting. -/
theorem checked_normal_linear_equiv : NormalLinearEquivStatement :=
  ParallelImplementation.RefinedNormalLinearEquiv.normal_linear_equiv
/-- **Math.** Exact audited derivative calculation at the zero fiber. -/
theorem checked_normal_endpoint_jet : NormalEndpointJetStatement :=
  ParallelImplementation.RefinedNormalEndpointJet.normal_endpoint_jet
/-- **Math.** These two accepted proofs are no longer unproved root parameters. -/
theorem public_after_twenty_nine (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (inverse : TubularChartInverseStatement.{u})
    (geometry : NormalGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_of_normal_frontier triangulate atlas checked_normal_linear_equiv
    checked_normal_endpoint_jet inverse geometry
#print axioms checked_normal_linear_equiv
#print axioms checked_normal_endpoint_jet
#print axioms public_after_twenty_nine
end PoincareConjecture.ProofContract.Refinement20260927
