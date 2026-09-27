import PoincareConjecture.ProofContract.Refinement20260927.MatchedBudget
import PoincareConjecture.ParallelImplementation.RefinedEpsilonNeckEmbedding
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** Exact independently recompiled embedding target; no changed statement. -/
theorem checked_epsilon_neck_embedding : EpsilonNeckEmbeddingStatement.{u} :=
  ParallelImplementation.RefinedEpsilonNeckEmbedding.epsilon_neck_embedding
/-- **Math.** A located cut of the explicit metric collar with all placement certificates. -/
def locatedMetricCut_checked {M : ClosedThreeManifold.{u}} (hsc : SimplyConnectedSpace M)
    (n : AmbientMetricNeck M) (p : Sphere2) : LocatedClosedCut n.closedCollar p :=
  locatedNeckCut hsc n.closedCollar (checked_epsilon_neck_embedding M n) p
/-- **Math.** Three research inputs remain. The repaired geometry uses located
cuts and identical per-site neck/metric data in its volume budget. -/
theorem public_after_thirteen (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u})
    (geometry : MatchedGeometryProducerStatement.{u} checked_epsilon_neck_embedding.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_of_matched_frontier triangulate atlas checked_epsilon_neck_embedding geometry
#print axioms checked_epsilon_neck_embedding
#print axioms locatedMetricCut_checked
#print axioms public_after_thirteen
end PoincareConjecture.ProofContract.Refinement20260927
