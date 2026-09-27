import PoincareConjecture.ProofContract.Refinement20260927.NeckLossBudget
import PoincareConjecture.ParallelImplementation.RefinedFiniteCapScaling
import PoincareConjecture.ParallelImplementation.RefinedUniformNeckAllowance
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set CriticalPath.SurgeryBudget
/-- **Math.** Exact bindings for the independently source-checked volume leaves. -/
theorem checked_finite_cap_scaling : FiniteCapScalingStatement.{u} :=
  ParallelImplementation.RefinedFiniteCapScaling.finite_cap_scaling
theorem checked_uniform_neck_allowance : UniformNeckAllowanceStatement.{u} :=
  ParallelImplementation.RefinedUniformNeckAllowance.uniform_neck_allowance
theorem checked_neck_local_loss {X Y : MeasuredSlice.{u}}
    {old : Set X} {new : Set Y} {B epsilon0 rho : ℝ}
    (hB : 0 ≤ B) (hrho : 0 < rho) (allowance : NeckAllowance.{u} B epsilon0)
    (w : NeckReplacementModel X Y old new B epsilon0 rho) :
    rho^3 + (Y.measure new).toReal ≤ (X.measure old).toReal :=
  neckReplacement_local_loss checked_finite_cap_scaling hB hrho allowance w
theorem public_after_twelve (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (geometry : NeckLossGeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_of_neck_loss_frontier triangulate atlas checked_uniform_neck_allowance
    checked_finite_cap_scaling geometry
#print axioms checked_finite_cap_scaling
#print axioms checked_uniform_neck_allowance
#print axioms checked_neck_local_loss
#print axioms public_after_twelve
end PoincareConjecture.ProofContract.Refinement20260927
