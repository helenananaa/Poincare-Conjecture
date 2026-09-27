import PoincareConjecture.ProofContract.Refinement20260927.RetractionModelRoot
import PoincareConjecture.ParallelImplementation.RefinedSphereEnergyApproximation
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
/-- **Math.** Returned C1-to-energy approximation target, independently rechecked. -/
theorem checked_sphere_energy_approximation : SphereEnergyApproximationStatement.{u} :=
  ParallelImplementation.RefinedSphereEnergyApproximation.sphere_energy_approximation
/-- **Math.** Old route remains available with only its three research inputs. -/
theorem public_after_twentyFive (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (geometry : RegularizedIntrinsicGeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_after_twentyFour triangulate atlas checked_sphere_energy_approximation geometry
/-- **Math.** New local-retraction construction has a checked consumer to the unchanged public target. -/
theorem public_of_smooth_retraction_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (forms : SmoothRetractionFormStatement.{u})
    (geometry : RetractionGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_of_retraction_model_frontier triangulate atlas forms checked_sphere_energy_approximation geometry
#print axioms checked_sphere_energy_approximation
#print axioms public_after_twentyFive
#print axioms public_of_smooth_retraction_frontier
end PoincareConjecture.ProofContract.Refinement20260927
