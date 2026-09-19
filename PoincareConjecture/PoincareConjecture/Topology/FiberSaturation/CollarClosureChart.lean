import PoincareConjecture.Topology.FiberSaturation.CollarFrontierZero
import PoincareConjecture.Topology.FiberSaturation.RestrictOpenEmbedding
import PoincareConjecture.Topology.FiberSaturation.CollarHalfParameter
import PoincareConjecture.Topology.FiberSaturation.CollarClosureHalfSpace
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- A selected genuine collar gives an explicit open half-collar chart of the
actual complementary closure, with zero section equal to the actual frontier.
This is topological; it neither supplies a smooth collar nor a global smooth atlas. -/
theorem oneSidedCollar_exists_closure_chart
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PreconnectedSpace X]
    {C : Set Y} {f : X × NeckParameter → Y} (hf : Topology.IsOpenEmbedding f)
    (hside : ∀ z, f z ∈ C ↔ (z.2 : ℝ) ≤ 0) {p : Y} {x : X}
    (hx : f (x, neckCenter) ∈ frontier (connectedComponentIn Cᶜ p)) :
    IsOpen {y : closure (connectedComponentIn Cᶜ p) | (y : Y) ∈ range f} ∧
    ∃ e : (X × Ico (0 : ℝ) 1) ≃ₜ
        {y : closure (connectedComponentIn Cᶜ p) // (y : Y) ∈ range f},
      ∀ z, ((e z).1 : Y) = f (z.1, halfCollarParameter z.2) ∧
        (((e z).1 : Y) ∈ frontier (connectedComponentIn Cᶜ p) ↔ (z.2 : ℝ) = 0) :=
/- SWARM_PROOF_BEGIN -/
by
  let S := closure (connectedComponentIn Cᶜ p)
  obtain ⟨eHalf, hHalf⟩ := exists_halfCollar_parameter_homeomorph (X := X)
  have hsets : {z : X × NeckParameter | 0 ≤ (z.2 : ℝ)} =
      {z : X × NeckParameter | f z ∈ S} := by
    ext z
    exact (oneSidedCollar_mem_closure_component_iff_nonneg hf hside hx z).symm
  obtain ⟨eRestr, hRestr, hOpen⟩ := openEmbedding_restrict_set_coordinates hf S
  refine ⟨hOpen, ?_⟩
  let e := eHalf.trans ((Homeomorph.setCongr hsets).trans eRestr)
  refine ⟨e, fun z => ?_⟩
  have hfwd : ((e z).1 : Y) = f (z.1, halfCollarParameter z.2) := by
    calc
      ((e z).1 : Y) = f (Homeomorph.setCongr hsets (eHalf z)).1 := hRestr _
      _ = f (eHalf z : X × NeckParameter) := rfl
      _ = f (z.1, halfCollarParameter z.2) := congrArg f (hHalf z)
  refine ⟨hfwd, ?_⟩
  rw [hfwd, oneSidedCollar_mem_frontier_iff_zero hf hside hx]
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation
