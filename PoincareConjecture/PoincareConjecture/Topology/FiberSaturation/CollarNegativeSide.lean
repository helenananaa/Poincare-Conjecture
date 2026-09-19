import PoincareConjecture.Topology.FiberSaturation.OneSidedCollar
import Mathlib.Tactic

set_option autoImplicit false
namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- The negative side of a genuine one-sided collar has an open
neighborhood inside C, so it cannot meet the closure of any complementary component. -/
theorem oneSidedCollar_negative_not_mem_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set Y} {f : X × NeckParameter → Y} (hf : Topology.IsOpenEmbedding f)
    (hside : ∀ z, f z ∈ C ↔ (z.2 : ℝ) ≤ 0) {p : Y} (z : X × NeckParameter)
    (hz : (z.2 : ℝ) < 0) :
    f z ∉ closure (connectedComponentIn Cᶜ p) :=
/- SWARM_PROOF_BEGIN -/
by
  intro hcl
  let U : Set (X × NeckParameter) := {w | (w.2 : ℝ) < 0}
  have hUopen : IsOpen U :=
    isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
  have himg : IsOpen (f '' U) := hf.isOpenMap U hUopen
  have hfz : f z ∈ f '' U := ⟨z, hz, rfl⟩
  have hUC : f '' U ⊆ C := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hside w).mpr (le_of_lt hw)
  obtain ⟨y, hyU, hyD⟩ := mem_closure_iff.mp hcl (f '' U) himg hfz
  exact connectedComponentIn_subset Cᶜ p hyD (hUC hyU)
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation
