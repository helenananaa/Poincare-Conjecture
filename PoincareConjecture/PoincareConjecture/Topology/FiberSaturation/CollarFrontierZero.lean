import PoincareConjecture.Topology.FiberSaturation.CollarClosureHalfSpace
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- The boundary in a selected collar is precisely the zero parameter section. -/
theorem oneSidedCollar_mem_frontier_iff_zero
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PreconnectedSpace X]
    {C : Set Y} {f : X × NeckParameter → Y} (hf : Topology.IsOpenEmbedding f)
    (hside : ∀ z, f z ∈ C ↔ (z.2 : ℝ) ≤ 0) {p : Y} {x : X}
    (hx : f (x, neckCenter) ∈ frontier (connectedComponentIn Cᶜ p))
    (z : X × NeckParameter) :
    f z ∈ frontier (connectedComponentIn Cᶜ p) ↔ (z.2 : ℝ) = 0 :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · intro hz
    have hnonneg : 0 ≤ (z.2 : ℝ) :=
      (oneSidedCollar_mem_closure_component_iff_nonneg hf hside hx z).mp
        (frontier_subset_closure hz)
    rcases hnonneg.eq_or_lt with hzero | hpos
    · exact hzero.symm
    · exfalso
      let U : Set (X × NeckParameter) := {w | 0 < (w.2 : ℝ)}
      have hUopen : IsOpen U :=
        isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)
      have himg : IsOpen (f '' U) := hf.isOpenMap U hUopen
      have hUD : f '' U ⊆ connectedComponentIn Cᶜ p := by
        rintro _ ⟨w, hw, rfl⟩
        exact (oneSidedCollar_mem_component_iff_pos hf hside hx w).mpr hw
      have hinter : f z ∈ interior (connectedComponentIn Cᶜ p) :=
        (himg.subset_interior_iff.mpr hUD) ⟨z, hpos, rfl⟩
      exact disjoint_interior_frontier.notMem_of_mem_left hinter hz
  · intro hz
    have hzcenter : z.2 = neckCenter := by
      apply Subtype.ext
      exact hz
    have hzeq : z = (z.1, neckCenter) := by
      ext <;> simp [hzcenter]
    rw [hzeq]
    exact oneSidedCollar_frontier_saturated hf hside hx z.1
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation
