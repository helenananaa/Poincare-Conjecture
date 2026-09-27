import PoincareConjecture.ProofContract.Refinement20260927.AmbientApproximationRoot
import PoincareConjecture.ParallelImplementation.RefinedCompactRetractionControl
import PoincareConjecture.ParallelImplementation.RefinedSphereCompositionEstimate
import PoincareConjecture.ParallelImplementation.RefinedAmbientSweepoutConfinement
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
open scoped Manifold ContDiff
/-- **Math.** Independent source rebuild of the actual compact-neighborhood estimate. -/
theorem checked_compact_retraction_control : CompactRetractionControlStatement.{u} :=
  ParallelImplementation.RefinedCompactRetractionControl.compact_retraction_control
/-- **Math.** Original fixed statement; repaired coercion proof is kernel-checked separately. -/
theorem checked_sphere_composition_estimate : SphereCompositionEstimateStatement :=
  ParallelImplementation.RefinedSphereCompositionEstimate.sphere_composition_estimate
/-- **Math.** Actual global smooth confinement preserving the entire closed parameter strip. -/
theorem checked_ambient_sweepout_confinement : AmbientSweepoutConfinementStatement :=
  ParallelImplementation.RefinedAmbientSweepoutConfinement.ambient_sweepout_confinement
/-- **Math.** Three proved inputs disappear; frames and endpoint correction are still explicit. -/
theorem AmbientApproximationData.toEmbedding_after_controls
    (frames : EmbeddedNormalFrameStatement.{u}) (correct : AmbientEndpointCorrectionStatement)
    {N : CompactSmoothThree.{u}} {g : Riemannian.RiemannianMetric (𝓡 3) N}
    {D : BasedSphereClass N} (r : AmbientApproximationData N g D) :
    ∃ out : EmbeddingApproximationData N g D, out.reference = r.reference :=
  r.toEmbedding frames checked_compact_retraction_control checked_sphere_composition_estimate
    correct checked_ambient_sweepout_confinement
/-- **Math.** The same V1 root, now with three fewer unproved proof parameters. -/
theorem public_after_thirty_six (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (frames : EmbeddedNormalFrameStatement.{u})
    (correct : AmbientEndpointCorrectionStatement) (geometry : AmbientGeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_of_ambient_frontier triangulate atlas frames checked_compact_retraction_control
    checked_sphere_composition_estimate correct checked_ambient_sweepout_confinement geometry
#print axioms checked_compact_retraction_control
#print axioms checked_sphere_composition_estimate
#print axioms checked_ambient_sweepout_confinement
#print axioms AmbientApproximationData.toEmbedding_after_controls
#print axioms public_after_thirty_six
end PoincareConjecture.ProofContract.Refinement20260927
