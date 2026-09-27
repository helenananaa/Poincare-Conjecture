import PoincareConjecture.ProofContract.Refinement20260927.AcceptedThirtySix
import PoincareConjecture.ParallelImplementation.RefinedEmbeddedNormalFrames
import PoincareConjecture.ParallelImplementation.RefinedAmbientEndpointCorrection
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
open scoped Manifold ContDiff
/-- **Math.** Actual normal frames for the supplied embedding, independently rebuilt. -/
theorem checked_embedded_normal_frames : EmbeddedNormalFrameStatement.{u} :=
  ParallelImplementation.RefinedEmbeddedNormalFrames.embedded_normal_frames
/-- **Math.** The exact correction formula and its factor-two bounds are now proved. -/
theorem checked_ambient_endpoint_correction : AmbientEndpointCorrectionStatement :=
  ParallelImplementation.RefinedAmbientEndpointCorrection.ambient_endpoint_correction
/-- **Math.** No unresolved frame, chart or inverse premise remains in this existence theorem. -/
theorem checked_embedded_normal_coordinates : EmbeddedNormalCoordinatesStatement.{u} :=
  coordinates_from_embedded_frames checked_embedded_normal_frames
/-- **Math.** Local smooth retraction for every supplied compact Euclidean embedding. -/
theorem checked_embedded_retraction (N : CompactSmoothThree.{u}) (n : ℕ)
    (e : CompactEuclideanEmbedding N n) :
    ∃ R : SmoothRetractionData N n, R.embed = e.map :=
  retraction_from_embedded_frames checked_embedded_normal_frames N n e
/-- **Math.** Whitney embedding and the checked construction give an actual local retraction. -/
theorem compact_smooth_local_retraction_exists (N : CompactSmoothThree.{u}) :
    ∃ n : ℕ, Nonempty (SmoothRetractionData N n) := by
  obtain ⟨n,⟨e⟩⟩ := compact_euclidean_embedding_exists N
  obtain ⟨R,_⟩ := checked_embedded_retraction N n e
  exact ⟨n,⟨R⟩⟩
/-- **Math.** The raw approximants are the only analytic witnesses still supplied here. -/
theorem AmbientApproximationData.toEmbedding_checked
    {N : CompactSmoothThree.{u}} {g : Riemannian.RiemannianMetric (𝓡 3) N}
    {D : BasedSphereClass N} (r : AmbientApproximationData N g D) :
    ∃ out : EmbeddingApproximationData N g D, out.reference = r.reference :=
  r.toEmbedding checked_embedded_normal_frames checked_compact_retraction_control
    checked_sphere_composition_estimate checked_ambient_endpoint_correction
    checked_ambient_sweepout_confinement
/-- **Math.** All completed subsidiary obligations disappear; three research inputs remain. -/
theorem public_after_thirty_eight (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (geometry : AmbientGeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_of_ambient_frontier triangulate atlas checked_embedded_normal_frames
    checked_compact_retraction_control checked_sphere_composition_estimate
    checked_ambient_endpoint_correction checked_ambient_sweepout_confinement geometry
#print axioms checked_embedded_normal_frames
#print axioms checked_ambient_endpoint_correction
#print axioms checked_embedded_normal_coordinates
#print axioms checked_embedded_retraction
#print axioms compact_smooth_local_retraction_exists
#print axioms AmbientApproximationData.toEmbedding_checked
#print axioms public_after_thirty_eight
end PoincareConjecture.ProofContract.Refinement20260927
