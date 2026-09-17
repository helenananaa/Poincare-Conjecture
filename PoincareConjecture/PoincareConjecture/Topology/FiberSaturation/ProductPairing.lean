import PoincareConjecture.Topology.FiberSaturation.CylinderHomeomorph
import PoincareConjecture.Topology.FiberSaturation.FrontierComponents

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- The two endpoint spheres are disjoint and are entire connected components
of the actual relative frontier. Every frontier component is one of them. -/
theorem sphere_product_two_frontier_components {J : Set ℝ} (hJ : IsOpen J)
    {U : Set (Sphere2 × J)} (hU : IsOpen U) (hconn : IsConnected U)
    (hfront : FiberSaturated (frontier U)) (hk : IsCompact (closure U)) :
    ∃ a b : J, (a : ℝ) < b ∧
      frontier U = (univ : Set Sphere2) ×ˢ ({a, b} : Set J) ∧
      Disjoint ((univ : Set Sphere2) ×ˢ ({a} : Set J)) (univ ×ˢ ({b} : Set J)) ∧
      (∀ x : Sphere2, connectedComponentIn (frontier U) (x, a) = univ ×ˢ ({a} : Set J)) ∧
      (∀ x : Sphere2, connectedComponentIn (frontier U) (x, b) = univ ×ˢ ({b} : Set J)) ∧
      (∀ p ∈ frontier U, connectedComponentIn (frontier U) p = univ ×ˢ ({a} : Set J) ∨
        connectedComponentIn (frontier U) p = univ ×ˢ ({b} : Set J)) := by
  obtain ⟨a, b, hab, ha, hb, _, _, hf⟩ := exists_closed_cylinder hJ hU hconn hfront hk
  let aJ : J := ⟨a, ha⟩
  let bJ : J := ⟨b, hb⟩
  have hne : aJ ≠ bJ := by
    intro h
    exact hab.ne (congrArg Subtype.val h)
  have hpair : frontier U = (univ : Set Sphere2) ×ˢ ({aJ, bJ} : Set J) := by
    rw [hf]
    ext p
    simp [aJ, bJ, Subtype.ext_iff]
  have hleft (x : Sphere2) : connectedComponentIn (frontier U) (x, aJ) =
      univ ×ˢ ({aJ} : Set J) := by
    rw [hpair]
    exact componentIn_two_fibers aJ bJ hne x
  have hright (x : Sphere2) : connectedComponentIn (frontier U) (x, bJ) =
      univ ×ˢ ({bJ} : Set J) := by
    rw [hpair, Set.pair_comm aJ bJ]
    exact componentIn_two_fibers bJ aJ hne.symm x
  refine ⟨aJ, bJ, hab, hpair, ?_, hleft, hright, ?_⟩
  · apply Set.disjoint_left.mpr
    intro p hp hq
    have hp' : p.2 = aJ := hp.2
    have hq' : p.2 = bJ := hq.2
    exact hne (hp'.symm.trans hq')
  · rintro ⟨x, t⟩ hp
    rw [hpair] at hp
    have ht : t = aJ ∨ t = bJ := by simpa using hp.2
    rcases ht with rfl | rfl
    · exact Or.inl (hleft x)
    · exact Or.inr (hright x)

/-- The verified topological product branch of the boundary-pairing node.
The sphere-bundle branch and smooth diffeomorphism statement are not asserted. -/
theorem relative_fiber_boundary_pairing_product {J : Set ℝ} (hJ : IsOpen J)
    (hinterval : OrdConnected J) {U : Set (Sphere2 × J)}
    (hU : IsOpen U) (hconn : IsConnected U)
    (hfront : FiberSaturated (frontier U)) (hk : IsCompact (closure U)) :
    Nonempty (↥(closure U) ≃ₜ (Sphere2 × Icc (0 : ℝ) 1)) ∧
    ∃ a b : J, (a : ℝ) < b ∧
      frontier U = (univ : Set Sphere2) ×ˢ ({a, b} : Set J) ∧
      Disjoint ((univ : Set Sphere2) ×ˢ ({a} : Set J)) (univ ×ˢ ({b} : Set J)) ∧
      (∀ x : Sphere2, connectedComponentIn (frontier U) (x, a) = univ ×ˢ ({a} : Set J)) ∧
      (∀ x : Sphere2, connectedComponentIn (frontier U) (x, b) = univ ×ˢ ({b} : Set J)) ∧
      (∀ p ∈ frontier U, connectedComponentIn (frontier U) p = univ ×ˢ ({a} : Set J) ∨
        connectedComponentIn (frontier U) p = univ ×ˢ ({b} : Set J)) :=
  ⟨sphere_product_closure_homeomorph hJ hinterval hU hconn hfront hk,
    sphere_product_two_frontier_components hJ hU hconn hfront hk⟩

end PoincareConjecture.Topology.FiberSaturation
