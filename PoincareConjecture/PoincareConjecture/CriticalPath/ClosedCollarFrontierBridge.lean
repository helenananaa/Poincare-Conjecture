import PoincareConjecture.Topology.FiberSaturation.ClosedCollarEndpoint
set_option autoImplicit false
namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- Transfer finite displayed-fiber components to an identified actual frontier.
The frontier-image equality is still an explicit input. -/
theorem closed_collar_frontier_fiber_component
    {Y : Type*} [TopologicalSpace Y] {a b : ℝ} {D : Set Y}
    {f : Sphere2 × Icc a b → Y} (hf : Topology.IsEmbedding f)
    {T : Set (Icc a b)} (hT : T.Finite)
    (hfrontier : frontier D = f '' (univ ×ˢ T))
    (t : Icc a b) (ht : t ∈ T) (x : Sphere2) :
    connectedComponentIn (frontier D) (f (x, t)) =
      f '' (univ ×ˢ ({t} : Set (Icc a b))) := by
  rw [hfrontier]
  exact closed_collar_displayed_fiber_component hf hT t ht x
end PoincareConjecture.Topology.FiberSaturation
