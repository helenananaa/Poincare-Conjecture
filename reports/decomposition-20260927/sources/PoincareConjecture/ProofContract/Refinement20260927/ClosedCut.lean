import PoincareConjecture.ProofContract.Refinement20260927.CapManifold
import PoincareConjecture.ProofContract.Refinement20260927.Root
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
/-- A genuine closed subset of the original manifold with its own boundary collar.
The interior chart data concerns only the original piece, not the cap quotient. -/
structure RegularSide (M : ClosedThreeManifold.{u}) (U : Set M) where
  closed : IsClosed U
  connected : ConnectedSpace U
  boundaryMap : Sphere2 → U
  boundaryEmbedding : Topology.IsEmbedding boundaryMap
  collar : Sphere2 × Ico (0 : ℝ) 1 → U
  collarEmbedding : Topology.IsOpenEmbedding collar
  collarZero : ∀ s, collar (s, ⟨0, by norm_num⟩) = boundaryMap s
  interiorCharts : ChartedSpace Euclidean3 {x : U // x ∉ Set.range boundaryMap}
def RegularSide.regularPiece {M : ClosedThreeManifold.{u}} {U : Set M}
    (s : RegularSide M U) : RegularCollaredPiece.{u} where
  carrier := U
  topology := inferInstance
  compact := isCompact_iff_compactSpace.mp s.closed.isCompact
  hausdorff := inferInstance
  boundaryMap := s.boundaryMap
  boundaryEmbedding := s.boundaryEmbedding
  collar := s.collar
  collarEmbedding := s.collarEmbedding
  collarZero := s.collarZero
  connected := s.connected
  interiorCharts := s.interiorCharts
/-- Data produced by a real separating cut. No quotient homeomorphism is assumed. -/
structure RegularClosedCut (M : ClosedThreeManifold.{u}) where
  U : Set M
  V : Set M
  left : RegularSide M U
  right : RegularSide M V
  covers : U ∪ V = Set.univ
  boundaryAgrees : ∀ s : Sphere2, (left.boundaryMap s).val = (right.boundaryMap s).val
  intersection : ∀ x : M, x ∈ U ∩ V ↔ ∃ s : Sphere2, (left.boundaryMap s).val = x
/-- Compact closed-cover reconstruction with the exact original inclusions. -/
def ClosedCoverGluingStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) (U V : Set M), IsClosed U → IsClosed V →
    U ∪ V = Set.univ → ∀ (bU : Sphere2 → U) (bV : Sphere2 → V),
    (∀ s, (bU s).val = (bV s).val) →
    (∀ x : M, x ∈ U ∩ V ↔ ∃ s : Sphere2, (bU s).val = x) →
    Nonempty (M ≃ₜ Quot (rawSeam bU bV (Homeomorph.refl Sphere2)))
/-- Cap manifolds and the raw realization are constructed, not added as fields. -/
def rawCut_of_closedCut (charts : CapChartStatement.{u})
    (openInterior : CapInteriorOpenStatement.{u}) (glue : ClosedCoverGluingStatement.{u})
    {M : ClosedThreeManifold.{u}} (c : RegularClosedCut M) :
    RawCutPresentation (cappedManifold charts openInterior c.left.regularPiece)
      (cappedManifold charts openInterior c.right.regularPiece) M where
  left := ⟨c.left.regularPiece.toCollaredPiece,
    cappedIdentification charts openInterior c.left.regularPiece⟩
  right := ⟨c.right.regularPiece.toCollaredPiece,
    cappedIdentification charts openInterior c.right.regularPiece⟩
  gluing := Homeomorph.refl Sphere2
  realization := Classical.choice (glue M c.U c.V c.left.closed c.right.closed
    c.covers c.left.boundaryMap c.right.boundaryMap c.boundaryAgrees c.intersection)
/-- A finite tree of actual closed-subset cuts. Its cap manifolds are the SAME
ones constructed by the chosen chart/interior inputs. Still an output, not Ricci flow. -/
inductive CollaredDecomposition (charts : CapChartStatement.{u})
    (openInterior : CapInteriorOpenStatement.{u}) : ClosedThreeManifold.{u} → Prop
  | sphereCovered {M} : HasSphereCover M → CollaredDecomposition charts openInterior M
  | handle {M} : IsSphereHandle M → CollaredDecomposition charts openInterior M
  | cut {M} (c : RegularClosedCut M) :
      CollaredDecomposition charts openInterior (cappedManifold charts openInterior c.left.regularPiece) →
      CollaredDecomposition charts openInterior (cappedManifold charts openInterior c.right.regularPiece) →
      CollaredDecomposition charts openInterior M
/-- Major geometry remains OPEN: actual finite cuts and terminal classifications.
The shared cap choices are explicit; no independent, mismatched witnesses are used. -/
def CollaredGeometricProducerStatement : Prop :=
  ∀ (charts : CapChartStatement.{u}) (openInterior : CapInteriorOpenStatement.{u}),
    ∀ M : ClosedThreeManifold.{u}, IsSmooth M → SimplyConnectedSpace M →
      CollaredDecomposition charts openInterior M
theorem collared_to_raw (charts : CapChartStatement.{u})
    (openInterior : CapInteriorOpenStatement.{u}) (glue : ClosedCoverGluingStatement.{u})
    {M : ClosedThreeManifold.{u}} (d : CollaredDecomposition charts openInterior M) :
    RawDecomposition M := by
  induction d with
  | sphereCovered h => exact .sphereCovered h
  | handle h => exact .handle h
  | cut c _ _ ihA ihB => exact .cut ⟨rawCut_of_closedCut charts openInterior glue c⟩ ihA ihB
theorem raw_geometry_of_collared_producer (charts : CapChartStatement.{u})
    (openInterior : CapInteriorOpenStatement.{u}) (glue : ClosedCoverGluingStatement.{u})
    (producer : CollaredGeometricProducerStatement.{u}) : RawGeometricProducerStatement.{u} := by
  intro M hsm hsc
  exact collared_to_raw charts openInterior glue (producer charts openInterior M hsm hsc)
/-- Eight explicit frontier obligations suffice for the unchanged public root.
This refines, rather than replaces or edits, the previously frozen six-input theorem. -/
theorem refined_frontier_implies_public
    (triangulate : TriangulationProducerStatement.{u}) (smoothPL : PLAtlasProducerStatement.{u})
    (charts : CapChartStatement.{u}) (complements : CapComplementStatement.{u})
    (markedGlue : MarkedGluingStatement.{u}) (openInterior : CapInteriorOpenStatement.{u})
    (closedGlue : ClosedCoverGluingStatement.{u})
    (producer : CollaredGeometricProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  frontier_implies_public triangulate smoothPL charts complements markedGlue
    (raw_geometry_of_collared_producer charts openInterior closedGlue producer)
#print axioms rawCut_of_closedCut
#print axioms collared_to_raw
#print axioms raw_geometry_of_collared_producer
#print axioms refined_frontier_implies_public
end PoincareConjecture.ProofContract.Refinement20260927
