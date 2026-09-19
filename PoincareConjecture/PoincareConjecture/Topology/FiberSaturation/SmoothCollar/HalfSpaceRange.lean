import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- The fixed model has exactly the geometric half-space, with its usual interior/frontier. -/
theorem halfSpaceModel_range_geometry {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    range (halfSpaceModel V) = {z : V × ℝ | 0 ≤ z.2} ∧
    interior (range (halfSpaceModel V)) = {z : V × ℝ | 0 < z.2} ∧
    frontier (range (halfSpaceModel V)) = {z : V × ℝ | z.2 = 0} :=
/- SWARM_PROOF_BEGIN -/
by
  have hrange : range (halfSpaceModel V) = (univ : Set V) ×ˢ Ici (0 : ℝ) := by
    change range (Subtype.val : HalfSpace V → V × ℝ) = _
    ext z
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hrange]
    ext z
    simp
  · rw [hrange, interior_prod_eq, interior_univ, interior_Ici]
    ext z
    simp
  · rw [hrange, frontier, closure_prod_eq, interior_prod_eq, closure_univ, interior_univ,
      closure_Ici, interior_Ici]
    ext z
    simp [not_lt]
    exact and_comm.trans (Iff.symm (le_antisymm_iff (a := z.2) (b := 0)))
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
