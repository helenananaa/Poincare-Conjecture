import PoincareConjecture.ProofContract.Refinement20260927.Cap
import PoincareConjecture.ProofContract.Refinement20260927.Smoothing
import PoincareConjecture.ProofContract.Proofs.TwoInputRootAssembly
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
/-- A finite RAW cutting expression. It has real cap quotients and marked piece
seams, not V1 coordinate balls or a connected-sum conclusion as fields.
This is an output certificate, NOT a definition or construction of Ricci flow. -/
inductive RawDecomposition : ClosedThreeManifold.{u} → Prop
  | sphereCovered {M} : HasSphereCover M → RawDecomposition M
  | handle {M} : IsSphereHandle M → RawDecomposition M
  | cut {A B M} : Nonempty (RawCutPresentation A B M) →
      RawDecomposition A → RawDecomposition B → RawDecomposition M
/-- Still a large research obligation: real flow, extinction, finite events,
cap identifications and exhaustive event topology must produce this certificate. -/
def RawGeometricProducerStatement : Prop :=
  ∀ M : ClosedThreeManifold.{u}, IsSmooth M → SimplyConnectedSpace M → RawDecomposition M
theorem rawDecomposition_to_standard
    (charts : CapChartStatement.{u}) (complements : CapComplementStatement.{u})
    (glue : MarkedGluingStatement.{u}) {M : ClosedThreeManifold.{u}}
    (d : RawDecomposition M) : StandardDecomposition M := by
  induction d with
  | sphereCovered h => exact .sphereCovered h
  | handle h => exact .handle h
  | cut h _ _ ihA ihB =>
    obtain ⟨p⟩ := h
    exact .connectedSum (rawCut_connectedSum charts complements glue p) ihA ihB
/-- Reuse of the previously checked finite-decomposition induction. -/
theorem standard_eliminates_context {M : ClosedThreeManifold.{u}}
    (d : StandardDecomposition M) :
    ∀ before after : List ClosedThreeManifold.{u},
      FiniteExtinctionTrace (before ++ after) →
      FiniteExtinctionTrace (before ++ M :: after) := by
  induction d with
  | sphereCovered h =>
    intro before after done
    exact .step (.discardCovered before after _ h) done
  | handle h =>
    intro before after done
    exact .step (.discardHandle before after _ h) done
  | connectedSum h _ _ ihA ihB =>
    intro before after done
    exact .step (.split before after _ _ _ h)
      (ihA before (_ :: after) (ihB before after done))
theorem geometric_of_raw_frontier
    (charts : CapChartStatement.{u}) (complements : CapComplementStatement.{u})
    (glue : MarkedGluingStatement.{u}) (producer : RawGeometricProducerStatement.{u}) :
    GeometricTraceStatement.{u} := by
  intro M hsm hsc
  exact standard_eliminates_context
    (rawDecomposition_to_standard charts complements glue (producer M hsm hsc)) [] [] .empty
/-- The CURRENT explicit frontier is sufficient for the EXACT frozen public root.
This is conditional. None of its six arguments is claimed proved here. -/
theorem frontier_implies_public
    (triangulate : TriangulationProducerStatement.{u}) (smoothPL : PLAtlasProducerStatement.{u})
    (charts : CapChartStatement.{u}) (complements : CapComplementStatement.{u})
    (glue : MarkedGluingStatement.{u}) (producer : RawGeometricProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  Proofs.topological_of_two_contracts
    (smoothing_of_finitePL_producers triangulate smoothPL)
    (geometric_of_raw_frontier charts complements glue producer)
#print axioms rawDecomposition_to_standard
#print axioms standard_eliminates_context
#print axioms geometric_of_raw_frontier
#print axioms frontier_implies_public
end PoincareConjecture.ProofContract.Refinement20260927
