import PoincareConjecture.ParallelMath.Transfer.NonNullInvariant
import PoincareConjecture.ParallelMath.Transfer.HomotopyLeftInverse
import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- A geometric comparison map homotopic to one with a left homotopy inverse preserves the same nontrivial maps. -/
theorem nonNull_comp_of_homotopic_transport
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (p q : C(Y,Z)) (r : C(Z,Y)) (hr : (r.comp p).Homotopic (ContinuousMap.id Y))
    (hpq : p.Homotopic q) (f : C(X,Y)) (hf : NonNull f) : NonNull (q.comp f) :=
/- SWARM_PROOF_BEGIN -/
by
  have hpf : NonNull (p.comp f) :=
    (nonNull_comp_iff_of_left_homotopy_inverse p r hr f).mpr hf
  have hpqf : (p.comp f).Homotopic (q.comp f) :=
    ContinuousMap.Homotopic.comp hpq (ContinuousMap.Homotopic.refl f)
  exact (nonNull_homotopic_iff hpqf).mp hpf
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
