import PoincareConjecture.ProofContract.Refinement20260927.ApproximateTransferRoot
import PoincareConjecture.ParallelImplementation.RefinedSphereEnergyContinuity
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
/-- **Math.** Exact source-recompiled leaf: local frames prove continuity,
without asserting that the pointwise selected global frame is continuous. -/
theorem checked_sphere_energy_continuity : SphereEnergyContinuityStatement.{u} :=
  ParallelImplementation.RefinedSphereEnergyContinuity.sphere_energy_continuity
/-- **Math.** The running comparison and the actual geometry remain explicit. -/
theorem public_after_twentyTwo (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    (geometry : ApproximateIntrinsicGeometryProducerStatement.{u} checked_sphere_energy_continuity.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_of_approximate_transfer_frontier triangulate atlas checked_sphere_energy_continuity compare geometry
#print axioms checked_sphere_energy_continuity
#print axioms public_after_twentyTwo
end PoincareConjecture.ProofContract.Refinement20260927
