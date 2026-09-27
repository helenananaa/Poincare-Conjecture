import PoincareConjecture.ProofContract.Refinement20260927.C1MetricMaps
import PoincareConjecture.ParallelImplementation.RefinedCylinderRestrictionEstimate
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
/-- **Math.** Fixed original restriction statement; the repaired source has been independently audited. -/
theorem checked_cylinder_restriction : CylinderRestrictionEstimateStatement :=
  ParallelImplementation.RefinedCylinderRestrictionEstimate.cylinder_restriction_estimate
/-- **Math.** Only compact C1 extension remains in the cylinder approximation construction. -/
theorem cylinder_c1_after_restriction (extend : CylinderCompactExtensionStatement) :
    CylinderC1ApproximationStatement :=
  cylinder_c1_after_uniform checked_cylinder_restriction extend
/-- **Math.** The repaired restriction proof is consumed by the actual unchanged V1 conclusion. -/
theorem public_after_forty_one (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (bound : C1AmbientFrameBoundStatement)
    (extend : CylinderCompactExtensionStatement) (geometry : C1GeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_of_c1_frontier triangulate atlas bound checked_cylinder_restriction extend geometry
#print axioms checked_cylinder_restriction
#print axioms cylinder_c1_after_restriction
#print axioms public_after_forty_one
end PoincareConjecture.ProofContract.Refinement20260927
