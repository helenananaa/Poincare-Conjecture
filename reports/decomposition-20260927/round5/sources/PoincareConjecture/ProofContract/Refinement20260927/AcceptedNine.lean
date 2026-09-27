import PoincareConjecture.ProofContract.Refinement20260927.CapRelabeling
import PoincareConjecture.ParallelImplementation.RefinedSideInteriorAtlas
import PoincareConjecture.ParallelImplementation.RefinedNegativeHalfCollar
import PoincareConjecture.ParallelImplementation.RefinedFiniteTimeline
import PoincareConjecture.ParallelImplementation.RefinedCapRelabeling
import PoincareConjecture.ProofContract.Proofs.ConnectedSumFactorsProof
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- Exact types: no unproved local topology parameters remain in these bindings. -/
theorem checked_side_atlas : SideInteriorAtlasStatement.{u} :=
  ParallelImplementation.RefinedSideInteriorAtlas.side_interior_atlas
theorem checked_negative_collar : NegativeHalfCollarStatement.{u} :=
  ParallelImplementation.RefinedNegativeHalfCollar.negative_half_collar
theorem checked_finite_timeline : FiniteTimelineStatement.{v} :=
  ParallelImplementation.RefinedFiniteTimeline.finite_timeline
theorem checked_cap_relabeling : CapRelabelingStatement.{u} :=
  ParallelImplementation.RefinedCapRelabeling.cap_relabeling
/-- Canonical actual closed cut of the SAME supplied collar. -/
def checked_neck_cut {M : ClosedThreeManifold.{u}} (hsc : SimplyConnectedSpace M)
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (hf : Topology.IsEmbedding f) (p : Sphere2) :
    RegularClosedCut M := closedCut_of_neck checked_side_atlas checked_negative_collar hsc f hf p
theorem checked_neck_connectedSum {M : ClosedThreeManifold.{u}}
    (hsc : SimplyConnectedSpace M) (f : Sphere2 × Icc (-1 : ℝ) 1 → M)
    (hf : Topology.IsEmbedding f) (p : Sphere2) :
    Nonempty (ConnectedSumPresentation
      (neckLeft checked_side_atlas checked_negative_collar hsc f hf p)
      (neckRight checked_side_atlas checked_negative_collar hsc f hf p) M) :=
  checked_closedCut_connectedSum (checked_neck_cut hsc f hf p)
theorem checked_neck_factors_simplyConnected {M : ClosedThreeManifold.{u}}
    (hsc : SimplyConnectedSpace M) (f : Sphere2 × Icc (-1 : ℝ) 1 → M)
    (hf : Topology.IsEmbedding f) (p : Sphere2) :
    SimplyConnectedSpace (neckLeft checked_side_atlas checked_negative_collar hsc f hf p) ∧
    SimplyConnectedSpace (neckRight checked_side_atlas checked_negative_collar hsc f hf p) :=
  Proofs.connectedSum_factors_proved _ _ _ (checked_neck_connectedSum hsc f hf p) hsc
/-- All nine former local leaves are actually consumed; budget and empty end remain explicit. -/
theorem checked_projection_trace {M : ClosedThreeManifold.{u}}
    (H : RelabeledProjection checked_side_atlas checked_negative_collar M)
    (hend : H.pre H.horizon = []) (budget : UniformEventBudget.{u} H.horizon H.events) :
    FiniteExtinctionTrace [M] :=
  projection_trace checked_finite_timeline checked_side_atlas checked_negative_collar
    (H.toProjection checked_cap_relabeling) hend budget
/-- Exactly three major research inputs remain; no unconditional Poincare claim. -/
theorem public_after_nine (triangulate : TriangulationProducerStatement.{u})
    (smoothPL : PLAtlasProducerStatement.{u}) (geometry : RelabeledProjectionProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_of_relabeled_projection triangulate smoothPL checked_side_atlas checked_negative_collar
    checked_finite_timeline checked_cap_relabeling geometry
#print axioms checked_side_atlas
#print axioms checked_negative_collar
#print axioms checked_finite_timeline
#print axioms checked_cap_relabeling
#print axioms checked_neck_cut
#print axioms checked_neck_connectedSum
#print axioms checked_neck_factors_simplyConnected
#print axioms checked_projection_trace
#print axioms public_after_nine
end PoincareConjecture.ProofContract.Refinement20260927
