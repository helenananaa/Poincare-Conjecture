import PoincareConjecture.Topology.FiberSaturation.Boundary
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
namespace PoincareConjecture.Topology.FiberSaturation
open Set

variable {Y : Type*} [TopologicalSpace Y]

/-- A connected exterior piece meeting every sufficiently local approach to
one component must lie entirely in that component. No saturation is assumed. -/
theorem exterior_piece_subset_component {U S V : Set Y} {p z : Y}
    (hS : IsPreconnected S) (hSU : S ⊆ U) (hV : IsOpen V) (hzV : z ∈ V)
    (hz : z ∈ closure (connectedComponentIn U p)) (hVS : V ∩ U ⊆ S) :
    S ⊆ connectedComponentIn U p := by
  obtain ⟨y, hyV, hyD⟩ := mem_closure_iff.mp hz V hV hzV
  have hyS : y ∈ S := hVS ⟨hyV, connectedComponentIn_subset U p hyD⟩
  rw [connectedComponentIn_eq hyD]
  exact hS.subset_connectedComponentIn hyS hSU

/-- In a locally connected ambient space, a complementary component has
frontier only on the actual frontier of the closed continuing region. -/
theorem complementary_component_frontier_subset [LocallyConnectedSpace Y]
    {C : Set Y} (hC : IsClosed C) {p : Y} (hp : p ∉ C) :
    frontier (connectedComponentIn Cᶜ p) ⊆ frontier C := by
  simpa only [frontier_compl] using
    frontier_componentIn_subset hC.isOpen_compl hp hC.isOpen_compl.connectedComponentIn

/-- A complementary component has empty frontier precisely in the excluded
whole-ambient-component case; here we use the implication needed by surgery. -/
theorem proper_complementary_component_frontier_nonempty
    {C : Set Y} {p : Y} (hp : p ∉ C)
    (hproper : connectedComponentIn Cᶜ p ≠ connectedComponent p) :
    (frontier (connectedComponentIn Cᶜ p)).Nonempty := by
  by_contra hn
  have hempty := Set.not_nonempty_iff_eq_empty.mp hn
  have hclopen := isClopen_iff_frontier_eq_empty.mpr hempty
  have hpD : p ∈ connectedComponentIn Cᶜ p := mem_connectedComponentIn hp
  have hself := isPreconnected_connectedComponentIn.connectedComponentIn hpD
  have hwhole := hclopen.connectedComponentIn_eq hpD
  exact hproper (hself.symm.trans hwhole)

end PoincareConjecture.Topology.FiberSaturation
