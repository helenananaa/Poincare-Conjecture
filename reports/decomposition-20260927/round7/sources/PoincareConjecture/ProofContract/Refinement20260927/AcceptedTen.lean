import PoincareConjecture.ProofContract.Refinement20260927.RicciVolumeBudget
import PoincareConjecture.ParallelImplementation.RefinedClosedScalarPropagation
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 CriticalPath.SurgeryBudget
/-- **Math.** Exact returned leaf, independently source-recompiled and audited. -/
theorem checked_closed_scalar : ClosedScalarPropagationStatement.{u} :=
  ParallelImplementation.RefinedClosedScalarPropagation.closed_scalar_propagation
/-- **Math.** The closed-endpoint obligation is discharged for actual PDE intervals. -/
theorem checked_ricci_interval_growth {X Y : MeasuredSlice.{u}} {C T : ℝ}
    (hC : 0 ≤ C) (e : RicciIntervalBridge X Y C T) :
    Y.volume ≤ Real.exp (C*T)*X.volume :=
  ricci_interval_volume_growth checked_closed_scalar hC e
/-- **Math.** Three large producers remain; not an unconditional Poincare theorem. -/
theorem public_after_ten (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u})
    (geometry : RicciBudgetGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_of_ricci_budget_frontier triangulate atlas checked_closed_scalar geometry
#print axioms checked_closed_scalar
#print axioms checked_ricci_interval_growth
#print axioms public_after_ten
end PoincareConjecture.ProofContract.Refinement20260927
