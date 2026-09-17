import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions.SumProd

set_option autoImplicit false

/-!
# Saturation of an open set by connected product fibers

The frontier hypothesis uses the actual topological frontier. It says that
if one point of a fiber is in the frontier, every point of that fiber is.
No geometric or analytic theorem is assumed.
-/

namespace PoincareConjecture.Topology.FiberSaturation
open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Membership is constant on each fiber of the second projection. -/
def FiberSaturated (s : Set (X × Y)) : Prop :=
  ∀ ⦃x₁ x₂ : X⦄ ⦃y : Y⦄, (x₁, y) ∈ s → (x₂, y) ∈ s

/-- An open set with saturated frontier has saturated membership,
provided the fibers are preconnected. -/
theorem fiberSaturated_of_frontier [PreconnectedSpace X]
    {U : Set (X × Y)} (hU : IsOpen U)
    (hfront : FiberSaturated (frontier U)) : FiberSaturated U := by
  intro x₁ x₂ y hx₁
  have hf : Continuous (fun x : X => (x, y)) :=
    continuous_id.prodMk continuous_const
  have hs : IsPreconnected (range (fun x : X => (x, y))) := by
    simpa only [image_univ] using isPreconnected_univ.image _ hf.continuousOn
  have hcl : closure U ∩ range (fun x : X => (x, y)) ⊆ U := by
    rintro _ ⟨hz, x, rfl⟩
    by_contra hn
    have hb : (x, y) ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hz, hn⟩
    have hb₁ : (x₁, y) ∈ frontier U := hfront hb
    rw [hU.frontier_eq] at hb₁
    exact hb₁.2 hx₁
  exact hs.subset_of_closure_inter_subset hU
    ⟨(x₁, y), ⟨x₁, rfl⟩, hx₁⟩ hcl ⟨x₂, rfl⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- A saturated set equals the cylinder over its second projection. -/
theorem FiberSaturated.eq_univ_prod_image {U : Set (X × Y)}
    (hU : FiberSaturated U) : U = univ ×ˢ (Prod.snd '' U) := by
  ext ⟨x, y⟩
  constructor
  · intro h
    exact ⟨mem_univ _, ⟨(x, y), h, rfl⟩⟩
  · rintro ⟨_, ⟨⟨x', y'⟩, h, heq⟩⟩
    change y' = y at heq
    subst y'
    exact hU h

/-- The canonical open base is exactly the second-coordinate image. -/
theorem eq_univ_prod_image_of_frontier [PreconnectedSpace X]
    {U : Set (X × Y)} (hU : IsOpen U)
    (hfront : FiberSaturated (frontier U)) :
    U = univ ×ˢ (Prod.snd '' U) :=
  (fiberSaturated_of_frontier hU hfront).eq_univ_prod_image

/-- Product-fiber saturation, with an open base and no choice of base. -/
theorem exists_open_base [PreconnectedSpace X]
    {U : Set (X × Y)} (hU : IsOpen U)
    (hfront : FiberSaturated (frontier U)) :
    ∃ A : Set Y, IsOpen A ∧ U = univ ×ˢ A :=
  ⟨Prod.snd '' U, isOpenMap_snd U hU,
    eq_univ_prod_image_of_frontier hU hfront⟩


omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Cylinders have saturated membership. -/
theorem fiberSaturated_univ_prod (A : Set Y) :
    FiberSaturated ((univ : Set X) ×ˢ A) := by
  intro x₁ x₂ y hy
  exact ⟨mem_univ _, hy.2⟩

/-- Concrete witnesses for the frontier-saturation hypothesis. -/
theorem frontier_fiberSaturated_univ_prod (A : Set Y) :
    FiberSaturated (frontier ((univ : Set X) ×ˢ A)) := by
  rw [frontier_univ_prod_eq]
  exact fiberSaturated_univ_prod _

end PoincareConjecture.Topology.FiberSaturation
