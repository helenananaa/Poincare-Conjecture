import PoincareConjecture.ProofContract.Refinement20260927.TubularRoot
import PoincareConjecture.ParallelImplementation.RefinedSmoothRetractionForm
import PoincareConjecture.ParallelImplementation.RefinedTubularInverseAssembly
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
/-- **Math.** Independently recompiled fixed proof, not a new assumption. -/
theorem checked_smooth_retraction_form : SmoothRetractionFormStatement.{u} :=
  ParallelImplementation.RefinedSmoothRetractionForm.smooth_retraction_form
/-- **Math.** Independently recompiled fixed proof, preserving the exact maps and image. -/
theorem checked_tubular_inverse_assembly : TubularInverseAssemblyStatement.{u} :=
  ParallelImplementation.RefinedTubularInverseAssembly.tubular_inverse_assembly
/-- **Math.** The two now-proved inputs disappear from the public conditional theorem. -/
theorem public_after_twenty_seven (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (geometry : TubularGeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_of_tubular_frontier triangulate atlas checked_smooth_retraction_form
    checked_tubular_inverse_assembly geometry
#print axioms checked_smooth_retraction_form
#print axioms checked_tubular_inverse_assembly
#print axioms public_after_twenty_seven
end PoincareConjecture.ProofContract.Refinement20260927
