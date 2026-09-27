import PoincareConjecture.ProofContract.Refinement20260927.Neck
import PoincareConjecture.ProofContract.Refinement20260927.AcceptedFive
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
/-- A finite certificate whose cuts are genuine embedded product collars.
The certificate is an output obligation, not a Ricci-flow definition. -/
inductive NeckDecomposition (charts : CapChartStatement.{u})
    (openInterior : CapInteriorOpenStatement.{u}) (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) : ClosedThreeManifold.{u} → Prop
  | sphereCovered {M} : HasSphereCover M → NeckDecomposition charts openInterior atlas negative M
  | handle {M} : IsSphereHandle M → NeckDecomposition charts openInterior atlas negative M
  | cut {M : ClosedThreeManifold.{u}} (hsc : SimplyConnectedSpace M)
      (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (hf : Topology.IsEmbedding f) (p : Sphere2) :
      NeckDecomposition charts openInterior atlas negative
        (cappedManifold charts openInterior (closedCut_of_neck atlas negative hsc f hf p).left.regularPiece) →
      NeckDecomposition charts openInterior atlas negative
        (cappedManifold charts openInterior (closedCut_of_neck atlas negative hsc f hf p).right.regularPiece) →
      NeckDecomposition charts openInterior atlas negative M
/-- Still RESEARCH: real controlled flow, finite extinction/events, neck/cap
identifications and ALL terminal classifications must construct this finite tree.
In particular no existence or smoothness of a capped Ricci flow is supplied here. -/
def NeckGeometricProducerStatement : Prop :=
  ∀ (charts : CapChartStatement.{u}) (openInterior : CapInteriorOpenStatement.{u})
    (atlas : SideInteriorAtlasStatement.{u}) (negative : NegativeHalfCollarStatement.{u}),
    ∀ M : ClosedThreeManifold.{u}, IsSmooth M → SimplyConnectedSpace M →
      NeckDecomposition charts openInterior atlas negative M
theorem neck_to_collared (charts : CapChartStatement.{u})
    (openInterior : CapInteriorOpenStatement.{u}) (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) {M : ClosedThreeManifold.{u}}
    (d : NeckDecomposition charts openInterior atlas negative M) :
    CollaredDecomposition charts openInterior M := by
  induction d with
  | sphereCovered h => exact .sphereCovered h
  | handle h => exact .handle h
  | cut hsc f hf p _ _ ihL ihR =>
    exact .cut (closedCut_of_neck atlas negative hsc f hf p) ihL ihR
/-- The two new leaves refine the existing large producer without changing its output. -/
theorem collared_geometry_of_necks (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) (producer : NeckGeometricProducerStatement.{u}) :
    CollaredGeometricProducerStatement.{u} := by
  intro charts openInterior M hsm hsc
  exact neck_to_collared charts openInterior atlas negative
    (producer charts openInterior atlas negative M hsm hsc)
/-- Five OPEN arguments: two ready topological leaves plus three large research producers. -/
theorem public_of_neck_frontier (triangulate : TriangulationProducerStatement.{u})
    (smoothPL : PLAtlasProducerStatement.{u}) (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u}) (producer : NeckGeometricProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_after_five triangulate smoothPL (collared_geometry_of_necks atlas negative producer)
#print axioms neck_to_collared
#print axioms collared_geometry_of_necks
#print axioms public_of_neck_frontier
end PoincareConjecture.ProofContract.Refinement20260927
