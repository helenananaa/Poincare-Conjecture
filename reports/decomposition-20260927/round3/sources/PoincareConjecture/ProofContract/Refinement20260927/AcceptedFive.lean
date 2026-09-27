import PoincareConjecture.ParallelImplementation.RefinedCapChart
import PoincareConjecture.ParallelImplementation.RefinedCapComplement
import PoincareConjecture.ParallelImplementation.RefinedMarkedGluing
import PoincareConjecture.ParallelImplementation.RefinedCapInteriorOpen
import PoincareConjecture.ParallelImplementation.RefinedClosedCoverGluing
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 ParallelImplementation
/-- Exact types of the five returned proofs, without extra assumptions. -/
theorem checked_cap_chart : CapChartStatement.{u} := RefinedCapChart.cap_chart
theorem checked_cap_complement : CapComplementStatement.{u} := RefinedCapComplement.cap_complement
theorem checked_marked_glue : MarkedGluingStatement.{u} := RefinedMarkedGluing.marked_gluing
theorem checked_interior_open : CapInteriorOpenStatement.{u} := RefinedCapInteriorOpen.cap_interior_open
theorem checked_closed_glue : ClosedCoverGluingStatement.{u} := RefinedClosedCoverGluing.closed_cover_gluing
/-- The concrete closed-cut to connected-sum adapter now has no open leaf inputs. -/
theorem checked_closedCut_connectedSum {M : ClosedThreeManifold.{u}}
    (c : RegularClosedCut M) :
    Nonempty (ConnectedSumPresentation
      (cappedManifold checked_cap_chart checked_interior_open c.left.regularPiece)
      (cappedManifold checked_cap_chart checked_interior_open c.right.regularPiece) M) :=
  rawCut_connectedSum checked_cap_chart checked_cap_complement checked_marked_glue
    (rawCut_of_closedCut checked_cap_chart checked_interior_open checked_closed_glue c)
/-- Five solved interfaces are actually consumed; three major producers remain open. -/
theorem public_after_five
    (triangulate : TriangulationProducerStatement.{u}) (smoothPL : PLAtlasProducerStatement.{u})
    (producer : CollaredGeometricProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  refined_frontier_implies_public triangulate smoothPL checked_cap_chart checked_cap_complement
    checked_marked_glue checked_interior_open checked_closed_glue producer
#print axioms checked_cap_chart
#print axioms checked_cap_complement
#print axioms checked_marked_glue
#print axioms checked_interior_open
#print axioms checked_closed_glue
#print axioms checked_closedCut_connectedSum
#print axioms public_after_five
end PoincareConjecture.ProofContract.Refinement20260927
