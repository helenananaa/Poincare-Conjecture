import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Actual nullhomotopy is invariant under a homotopy of maps. -/
theorem nonNull_homotopic_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X,Y)} (h : f.Homotopic g) : NonNull f ↔ NonNull g :=
/- SWARM_PROOF_BEGIN -/
by
  unfold NonNull
  constructor
  · exact mt fun ⟨y, hy⟩ => ⟨y, h.trans hy⟩
  · exact mt fun ⟨y, hy⟩ => ⟨y, h.symm.trans hy⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
