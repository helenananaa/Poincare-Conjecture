import PoincareConjecture.Topology.FiberSaturation.NeckCoordinates
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FunProp

set_option autoImplicit false

noncomputable section

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- Remove the redundant ambient-interval subtype from a closed cylinder.
The inclusion of the whole closed interval in the parameter domain is explicit. -/
def relativeClosedCylinderHomeomorph {X : Type*} [TopologicalSpace X]
    {J : Set ℝ} {a b : ℝ} (hsub : Icc a b ⊆ J) :
    ↥((univ : Set X) ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc a b)) ≃ₜ
      (X × Icc a b) where
  toFun p := (p.1.1, ⟨(p.1.2 : ℝ), p.2.2⟩)
  invFun p := ⟨(p.1, ⟨(p.2 : ℝ), hsub p.2.2⟩), mem_univ _, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The explicit normalization of a relative closed cylinder to unit length. -/
def relativeClosedCylinderUnitHomeomorph {X : Type*} [TopologicalSpace X]
    {J : Set ℝ} {a b : ℝ} (hsub : Icc a b ⊆ J) (hab : a < b) :
    ↥((univ : Set X) ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc a b)) ≃ₜ
      (X × Icc (0 : ℝ) 1) :=
  (relativeClosedCylinderHomeomorph hsub).trans
    ((Homeomorph.refl X).prodCongr (iccHomeoI a b hab))

/-- The product-neck case: the actual closure is homeomorphic to a closed
unit cylinder. This is a topological, not a smooth, classification. -/
theorem sphere_product_closure_homeomorph {J : Set ℝ} (hJ : IsOpen J)
    (hinterval : OrdConnected J) {U : Set (Sphere2 × J)}
    (hU : IsOpen U) (hconn : IsConnected U)
    (hfront : FiberSaturated (frontier U)) (hk : IsCompact (closure U)) :
    Nonempty (↥(closure U) ≃ₜ (Sphere2 × Icc (0 : ℝ) 1)) := by
  obtain ⟨a, b, hab, ha, hb, _, hcl, _⟩ :=
    exists_closed_cylinder hJ hU hconn hfront hk
  exact ⟨(Homeomorph.setCongr hcl).trans
    (relativeClosedCylinderUnitHomeomorph (hinterval.out ha hb) hab)⟩

/-- The same classification in supplied neck coordinates. No existence of
such coordinates is assumed as a conclusion or asserted without proof. -/
theorem neck_closure_homeomorph_unitCylinder {N : Type*} [TopologicalSpace N]
    {J : Set ℝ} (hJ : IsOpen J) (hinterval : OrdConnected J)
    (e : N ≃ₜ (Sphere2 × J)) {U : Set N} (hU : IsOpen U)
    (hconn : IsConnected U) (hfront : FiberSaturated (e '' frontier U))
    (hk : IsCompact (closure U)) :
    Nonempty (↥(closure U) ≃ₜ (Sphere2 × Icc (0 : ℝ) 1)) := by
  have hf : FiberSaturated (frontier (e '' U)) := by
    rwa [e.image_frontier] at hfront
  have hc : IsCompact (closure (e '' U)) := by
    rw [← e.image_closure]
    exact hk.image e.continuous
  obtain ⟨k⟩ := sphere_product_closure_homeomorph hJ hinterval
    (e.isOpenMap _ hU) (hconn.image _ e.continuous.continuousOn) hf hc
  exact ⟨(e.image (closure U)).trans ((Homeomorph.setCongr (e.image_closure U)).trans k)⟩

end PoincareConjecture.Topology.FiberSaturation
