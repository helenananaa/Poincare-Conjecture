import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- A map with a genuine left homotopy inverse preserves and reflects non-nullhomotopic maps. -/
theorem nonNull_comp_iff_of_left_homotopy_inverse
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (p : C(Y,Z)) (r : C(Z,Y)) (hr : (r.comp p).Homotopic (ContinuousMap.id Y))
    (f : C(X,Y)) : NonNull (p.comp f) ↔ NonNull f :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · intro h ⟨y, hy⟩
    refine h ⟨p y, ?_⟩
    simpa [ContinuousMap.comp_const] using
      ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl p) hy
  · intro h ⟨z, hz⟩
    refine h ⟨r z, ?_⟩
    have h₁ : (r.comp (p.comp f)).Homotopic f := by
      simpa [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
        ContinuousMap.Homotopic.comp hr (ContinuousMap.Homotopic.refl f)
    have h₂ : (r.comp (p.comp f)).Homotopic (ContinuousMap.const X (r z)) := by
      simpa [ContinuousMap.comp_const] using
        ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl r) hz
    exact h₁.symm.trans h₂
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
