import PoincareConjecture.ProofContract.Refinement20260927.EmbeddedRoot
import PoincareConjecture.ParallelImplementation.RefinedTubularChartInverse
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
/-- **Math.** Independently recompiled local inverse proof; no unproved analytic input remains here. -/
theorem checked_tubular_chart_inverse : TubularChartInverseStatement.{u} :=
  ParallelImplementation.RefinedTubularChartInverse.tubular_chart_inverse
/-- **Math.** All three round20 leaves are now proved and consumed, using the same supplied data. -/
theorem checked_normal_coordinate_retraction {N : CompactSmoothThree.{u}} {n : ℕ}
    {e : CompactEuclideanEmbedding N n} (T : NormalCoordinateTube e) :
    ∃ R : SmoothRetractionData N n, R.embed = e.map :=
  T.toRetraction checked_normal_linear_equiv checked_normal_endpoint_jet checked_tubular_chart_inverse
/-- **Math.** Only the four genuinely new independent leaves remain for embedding-to-retraction. -/
theorem embedded_retraction_from_four_leaves (frames : EmbeddedNormalFrameStatement.{u})
    (transport : NormalFrameTransportStatement.{u})
    (parametrize : NormalBundleParametrizationStatement.{u})
    (regularity : NormalParametrizationRegularityStatement.{u})
    (N : CompactSmoothThree.{u}) (n : ℕ) (e : CompactEuclideanEmbedding N n) :
    ∃ R : SmoothRetractionData N n, R.embed = e.map :=
  embedded_retraction_of_frame_leaves frames transport parametrize regularity
    checked_tubular_chart_inverse N n e
/-- **Math.** The proved local-inverse obligation is removed from the actual V1 root signature. -/
theorem public_after_thirty (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u})
    (frames : EmbeddedNormalFrameStatement.{u}) (transport : NormalFrameTransportStatement.{u})
    (parametrize : NormalBundleParametrizationStatement.{u})
    (regularity : NormalParametrizationRegularityStatement.{u})
    (geometry : EmbeddingGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_of_embedded_frontier triangulate atlas checked_tubular_chart_inverse
    frames transport parametrize regularity geometry
#print axioms checked_tubular_chart_inverse
#print axioms checked_normal_coordinate_retraction
#print axioms embedded_retraction_from_four_leaves
#print axioms public_after_thirty
end PoincareConjecture.ProofContract.Refinement20260927
