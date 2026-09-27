import PoincareConjecture.ProofContract.Refinement20260927.AcceptedThirty
import PoincareConjecture.ParallelImplementation.RefinedNormalFrameTransport
import PoincareConjecture.ParallelImplementation.RefinedNormalBundleParametrization
import PoincareConjecture.ParallelImplementation.RefinedNormalParametrizationRegularity
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
/-- **Math.** Independently recompiled finite-sum transport proof. -/
theorem checked_normal_frame_transport : NormalFrameTransportStatement.{u} :=
  ParallelImplementation.RefinedNormalFrameTransport.normal_frame_transport
/-- **Math.** Independently recompiled actual normal-bundle chart construction. -/
theorem checked_normal_bundle_parametrization : NormalBundleParametrizationStatement.{u} :=
  ParallelImplementation.RefinedNormalBundleParametrization.normal_bundle_parametrization
/-- **Math.** Independently recompiled local smoothness proof. -/
theorem checked_normal_parametrization_regularity : NormalParametrizationRegularityStatement.{u} :=
  ParallelImplementation.RefinedNormalParametrizationRegularity.normal_parametrization_regularity
/-- **Math.** Only the geometric local-frame existence input remains. -/
theorem coordinates_from_embedded_frames (frames : EmbeddedNormalFrameStatement.{u}) :
    EmbeddedNormalCoordinatesStatement.{u} :=
  embedded_normal_coordinates_of_leaves frames checked_normal_frame_transport
    checked_normal_bundle_parametrization checked_normal_parametrization_regularity
/-- **Math.** Same-embedding retraction; no parameter-chart or local-inverse input. -/
theorem retraction_from_embedded_frames (frames : EmbeddedNormalFrameStatement.{u})
    (N : CompactSmoothThree.{u}) (n : ℕ) (e : CompactEuclideanEmbedding N n) :
    ∃ R : SmoothRetractionData N n, R.embed = e.map := by
  obtain ⟨T⟩ := coordinates_from_embedded_frames frames N n e
  exact checked_normal_coordinate_retraction T
/-- **Math.** Three newly proved leaves are removed from the public conditional signature. -/
theorem public_after_thirty_three (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (frames : EmbeddedNormalFrameStatement.{u})
    (geometry : EmbeddingGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_after_thirty triangulate atlas frames checked_normal_frame_transport
    checked_normal_bundle_parametrization checked_normal_parametrization_regularity geometry
#print axioms checked_normal_frame_transport
#print axioms checked_normal_bundle_parametrization
#print axioms checked_normal_parametrization_regularity
#print axioms coordinates_from_embedded_frames
#print axioms retraction_from_embedded_frames
#print axioms public_after_thirty_three
end PoincareConjecture.ProofContract.Refinement20260927
