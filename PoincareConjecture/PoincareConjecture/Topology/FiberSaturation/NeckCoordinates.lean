import PoincareConjecture.Topology.FiberSaturation.Blueprint
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- Closed-cylinder description of the relative closure. This is a
set-theoretic/topological interface, not a smooth collar classification. -/
theorem exists_closed_cylinder {J : Set ℝ} (hJ : IsOpen J)
    {U : Set (Sphere2 × J)} (hU : IsOpen U) (hconn : IsConnected U)
    (hfront : FiberSaturated (frontier U)) (hk : IsCompact (closure U)) :
    ∃ a b : ℝ, a < b ∧ a ∈ J ∧ b ∈ J ∧
      U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo a b) ∧
      closure U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc a b) ∧
      frontier U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' {a, b}) := by
  obtain ⟨a, b, hab, ha, hb, hu, hf⟩ :=
    exists_interval_of_compact_closure hJ hU hconn hfront hk
  refine ⟨a, b, hab, ha, hb, hu, ?_, hf⟩
  rw [hu, closure_prod_eq, closure_univ,
    ← hJ.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val, closure_Ioo hab.ne]

/-- Transport the proven cylinder description through genuine neck coordinates.
Only a homeomorphism is used; no smoothness or bundle classification is claimed. -/
theorem neck_coordinates_cylinder {N : Type*} [TopologicalSpace N]
    {J : Set ℝ} (hJ : IsOpen J) (e : N ≃ₜ (Sphere2 × J))
    {U : Set N} (hU : IsOpen U) (hconn : IsConnected U)
    (hfront : FiberSaturated (e '' frontier U)) (hk : IsCompact (closure U)) :
    ∃ a b : ℝ, a < b ∧ a ∈ J ∧ b ∈ J ∧
      U = e ⁻¹' (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo a b)) ∧
      closure U = e ⁻¹' (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc a b)) ∧
      frontier U = e ⁻¹' (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' {a, b})) := by
  have ho : IsOpen (e '' U) := e.isOpenMap _ hU
  have hc : IsConnected (e '' U) := hconn.image _ e.continuous.continuousOn
  have hf : FiberSaturated (frontier (e '' U)) := by
    rwa [e.image_frontier] at hfront
  have hkc : IsCompact (closure (e '' U)) := by
    rw [← e.image_closure]
    exact hk.image e.continuous
  obtain ⟨a, b, hab, ha, hb, hu, hcl, hfr⟩ := exists_closed_cylinder hJ ho hc hf hkc
  refine ⟨a, b, hab, ha, hb, ?_, ?_, ?_⟩
  · rw [← hu, preimage_image_eq _ e.injective]
  · rw [← hcl, ← e.image_closure, preimage_image_eq _ e.injective]
  · rw [← hfr, ← e.image_frontier, preimage_image_eq _ e.injective]

end PoincareConjecture.Topology.FiberSaturation
