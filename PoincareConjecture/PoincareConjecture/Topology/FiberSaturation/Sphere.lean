import PoincareConjecture.Topology.FiberSaturation.Interval
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- The actual unit two-sphere in Euclidean three-space. -/
abbrev Sphere2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Connectedness is proved, not an extra hypothesis of the neck theorems. -/
instance sphere2_connectedSpace : ConnectedSpace Sphere2 := by
  apply isConnected_iff_connectedSpace.mp
  apply isConnected_sphere ?_ _ (by norm_num)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

/-- First clause of the product-neck saturation statement. -/
theorem sphere_neck_fiber_saturation {J : Set ℝ}
    {U : Set (Sphere2 × J)} (hU : IsOpen U)
    (hfront : FiberSaturated (frontier U)) :
    ∃ A : Set J, IsOpen A ∧ U = univ ×ˢ A :=
  exists_open_base hU hfront

/-- Compact relative closure gives precisely two complete frontier spheres.
Nonempty frontier excludes the empty-open-set edge case. -/
theorem sphere_neck_two_frontier_spheres {J : Set ℝ} (hJ : IsOpen J)
    {U : Set (Sphere2 × J)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hfront : FiberSaturated (frontier U)) (hcompact : IsCompact (closure U))
    (hne : (frontier U).Nonempty) :
    ∃ a b : ℝ, a < b ∧ a ∈ J ∧ b ∈ J ∧
      U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo a b) ∧
      frontier U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' {a, b}) := by
  have hUne : U.Nonempty := by
    by_contra h
    have hz : U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [hz] at hne
  exact exists_interval_of_compact_closure hJ hU ⟨hUne, hconn⟩ hfront hcompact


/-- First clause with the interval property explicit in the real parameter. -/
theorem sphere_neck_open_interval {J : Set ℝ} (hJ : IsOpen J)
    {U : Set (Sphere2 × J)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hfront : FiberSaturated (frontier U)) :
    ∃ A : Set ℝ, IsOpen A ∧ OrdConnected A ∧ A ⊆ J ∧
      U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' A) :=
  exists_open_ordConnected_base hJ hU hconn hfront

end PoincareConjecture.Topology.FiberSaturation
