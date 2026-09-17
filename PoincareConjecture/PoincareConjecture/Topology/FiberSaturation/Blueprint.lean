import PoincareConjecture.Topology.FiberSaturation.Sphere

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- Both clauses of `lem:fiber-saturation-from-spherical-frontier`.
The base is open and order-connected, allowing the empty case; all frontiers
and closures are taken in the relative product `Sphere2 × J`.
Source: primary blueprint, Topological Endgame, MT Appendices A.20--A.21.
The result allows any open `J`, hence also every nonempty open interval. -/
theorem fiber_saturation_from_spherical_frontier {J : Set ℝ} (hJ : IsOpen J)
    {U : Set (Sphere2 × J)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hfront : FiberSaturated (frontier U)) :
    (∃ A : Set ℝ, IsOpen A ∧ OrdConnected A ∧ A ⊆ J ∧
      U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' A)) ∧
    (IsCompact (closure U) → (frontier U).Nonempty →
      ∃ a b : ℝ, a < b ∧ a ∈ J ∧ b ∈ J ∧
        U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo a b) ∧
        frontier U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' {a, b})) := by
  constructor
  · exact sphere_neck_open_interval hJ hU hconn hfront
  · exact sphere_neck_two_frontier_spheres hJ hU hconn hfront

end PoincareConjecture.Topology.FiberSaturation
