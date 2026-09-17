import PoincareConjecture.Topology.FiberSaturation.Boundary
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- In a union of two disjoint closed sets, the preconnected side containing
x is exactly the connected component of x in the union. -/
theorem componentIn_disjoint_closed_union {Z : Type*} [TopologicalSpace Z]
    {A B : Set Z} (hA : IsClosed A) (hB : IsClosed B)
    (hconn : IsPreconnected A) (hdis : Disjoint A B) {x : Z} (hx : x ∈ A) :
    connectedComponentIn (A ∪ B) x = A := by
  apply Subset.antisymm ?_ (hconn.subset_connectedComponentIn hx subset_union_left)
  intro z hz
  by_contra hn
  have hxC := mem_connectedComponentIn (show x ∈ A ∪ B from Or.inl hx)
  have hzB : z ∈ B := (connectedComponentIn_subset (A ∪ B) x hz).resolve_left hn
  obtain ⟨w, _, hwA, hwB⟩ :=
    (isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn)
      A B hA hB (connectedComponentIn_subset (A ∪ B) x)
      ⟨x, hxC, hx⟩ ⟨z, hz, hzB⟩
  exact Set.disjoint_left.mp hdis hwA hwB

/-- Every member of a finite pairwise-disjoint closed preconnected family
is an entire component of the union, rather than merely a subset of one. -/
theorem componentIn_finite_disjoint_closed {Z ι : Type*} [TopologicalSpace Z]
    [Finite ι] (F : ι → Set Z) (hclosed : ∀ i, IsClosed (F i))
    (hconn : ∀ i, IsPreconnected (F i))
    (hdis : Pairwise (fun i j => Disjoint (F i) (F j)))
    (i : ι) {x : Z} (hx : x ∈ F i) :
    connectedComponentIn (⋃ j, F j) x = F i := by
  classical
  let R : Set Z := ⋃ j : {j : ι // j ≠ i}, F j.1
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hclosed j.1)
  have hFR : Disjoint (F i) R := by
    apply Set.disjoint_left.mpr
    intro z hzi hzR
    obtain ⟨j, hzj⟩ := mem_iUnion.mp hzR
    exact Set.disjoint_left.mp (hdis j.2.symm) hzi hzj
  have hUnion : (⋃ j, F j) = F i ∪ R := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hz
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hzj)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hzj⟩)
    · rintro (hzi | hzR)
      · exact mem_iUnion.mpr ⟨i, hzi⟩
      · obtain ⟨j, hzj⟩ := mem_iUnion.mp hzR
        exact mem_iUnion.mpr ⟨j.1, hzj⟩
  rw [hUnion]
  exact componentIn_disjoint_closed_union (hclosed i) hR (hconn i) hFR hx

/-- Each of two distinct parameter fibers is an entire component of their
union. Connectedness is supplied by the fiber, not by an unproved boundary assumption. -/
theorem componentIn_two_fibers {X B : Type*} [TopologicalSpace X]
    [TopologicalSpace B] [PreconnectedSpace X] [T1Space B]
    (a b : B) (hab : a ≠ b) (x : X) :
    connectedComponentIn ((univ : Set X) ×ˢ ({a, b} : Set B)) (x, a) =
      univ ×ˢ ({a} : Set B) := by
  have heq : ((univ : Set X) ×ˢ ({a, b} : Set B)) =
      (univ ×ˢ ({a} : Set B)) ∪ (univ ×ˢ ({b} : Set B)) := by
    ext p
    simp
  have hd : Disjoint ((univ : Set X) ×ˢ ({a} : Set B))
      (univ ×ˢ ({b} : Set B)) := by
    apply Set.disjoint_left.mpr
    intro p ha hb
    have hpa : p.2 = a := ha.2
    have hpb : p.2 = b := hb.2
    exact hab (hpa.symm.trans hpb)
  rw [heq]
  exact componentIn_disjoint_closed_union (isClosed_univ.prod isClosed_singleton)
    (isClosed_univ.prod isClosed_singleton)
    (isPreconnected_univ.prod isPreconnected_singleton) hd ⟨mem_univ _, rfl⟩

end PoincareConjecture.Topology.FiberSaturation
