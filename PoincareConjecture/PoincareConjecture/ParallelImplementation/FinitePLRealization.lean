import Mathlib

/-!
# Finite abstract complexes and their standard geometric realization

This module supplies a finite combinatorial object and its standard barycentric realization. It
does not assert the dimension, link, or PL-manifold conditions needed for a triangulated
3-manifold, and it contains no smoothability or Poincare result.
-/

noncomputable section

namespace PoincareConjecture.ParallelImplementation.FinitePLRealization

/-- An abstract simplicial complex on a finite vertex type. -/
abbrev FiniteAbstractComplex (V : Type*) [Fintype V] :=
  AbstractSimplicialComplex V

/-- Combinatorial dimension is bounded by `d` when every face has at most `d + 1` vertices. -/
def dimensionAtMost {V : Type*} [Fintype V]
    (K : FiniteAbstractComplex V) (d : ℕ) : Prop :=
  ∀ s ∈ K.faces, s.card ≤ d + 1

/-- The purely combinatorial dimension bound used for finite PL three-dimensional candidates. -/
def IsCombinatorialThreeDimensional {V : Type*} [Fintype V]
    (K : FiniteAbstractComplex V) : Prop :=
  dimensionAtMost K 3

/-- The abstract link of a face, consisting of nonempty disjoint faces whose union remains a face.

This is the abstract face condition only; no sphericality or PL-manifold condition is asserted. -/
def abstractLink {V : Type*} [Fintype V] [DecidableEq V]
    (K : FiniteAbstractComplex V) (s : Finset V) (_hs : s ∈ K.faces) :
    PreAbstractSimplicialComplex V where
  faces := {t | t.Nonempty ∧ Disjoint t s ∧ t ∪ s ∈ K.faces}
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    intro u hut hu
    refine ⟨hu, Finset.disjoint_of_subset_left hut ht.2.1, ?_⟩
    exact (K.isRelLowerSet_faces ht.2.2).2
      (Finset.union_subset_union hut (by intro x hx; exact hx))
      hu.inl

/-- The standard basis vector for a vertex, used as its barycentric coordinate point. -/
def barycentricVertex {V : Type*} [DecidableEq V] (v : V) : V → ℝ :=
  Pi.single v 1

/-- The standard realization places vertex `v` at the basis vector `e_v` in `V → ℝ`. -/
def realization {V : Type*} [Fintype V] [DecidableEq V]
    (K : FiniteAbstractComplex V) : Geometry.SimplicialComplex ℝ (V → ℝ) :=
  Geometry.SimplicialComplex.ofAffineIndependent
    (K.toPreAbstractSimplicialComplex.map barycentricVertex)
    ((Pi.linearIndependent_single_one V ℝ).affineIndependent.range.mono (by
      intro x hx
      change x ∈ Set.range barycentricVertex
      rcases Set.mem_iUnion₂.mp hx with ⟨t, ht, hxt⟩
      change t ∈ Set.image (fun s : Finset V => s.image barycentricVertex) K.faces at ht
      simp only [Set.mem_image] at ht
      rcases ht with ⟨s, hs, hst⟩
      subst t
      have hxt : x ∈ s.image barycentricVertex := Finset.mem_coe.mp hxt
      rcases Finset.mem_image.mp hxt with ⟨v, hv, hvx⟩
      exact ⟨v, hvx⟩))

/-- A face of the abstract complex gives the corresponding geometric face. -/
theorem abstract_face_realizes {V : Type*} [Fintype V] [DecidableEq V]
    (K : FiniteAbstractComplex V) {s : Finset V} (hs : s ∈ K.faces) :
    s.image barycentricVertex ∈ (realization K).faces := by
  change s.image barycentricVertex ∈
    (K.toPreAbstractSimplicialComplex.map barycentricVertex).faces
  exact Set.mem_image_of_mem _ hs

/-- Every geometric face in the standard realization comes from an abstract face. -/
theorem realized_face_originates {V : Type*} [Fintype V] [DecidableEq V]
    (K : FiniteAbstractComplex V) {t : Finset (V → ℝ)}
    (ht : t ∈ (realization K).faces) :
    ∃ s ∈ K.faces, s.image barycentricVertex = t := by
  change t ∈ (K.toPreAbstractSimplicialComplex.map barycentricVertex).faces at ht
  simpa only [PreAbstractSimplicialComplex.map, Set.mem_image] using ht

/-- The standard barycentric vertex map is injective. -/
theorem barycentricVertex_injective {V : Type*} [DecidableEq V] :
    Function.Injective (barycentricVertex (V := V)) := by
  intro v w h
  have hcoord := congrArg (fun f : V → ℝ => f v) h
  by_contra hvw
  simp [barycentricVertex, hvw] at hcoord

/-- Intersections of vertex sets in the realization are exactly images of abstract intersections.
-/
theorem barycentric_face_intersection {V : Type*} [Fintype V] [DecidableEq V]
    (s t : Finset V) :
    (↑(s.image barycentricVertex) : Set (V → ℝ)) ∩
      (↑(t.image barycentricVertex) : Set (V → ℝ)) =
        (↑((s ∩ t).image barycentricVertex) : Set (V → ℝ)) := by
  simp only [Finset.coe_image, Finset.coe_inter]
  exact (Set.image_inter barycentricVertex_injective).symm

/-- Two realized abstract faces meet in the realization of their common abstract face. -/
theorem convexHull_abstract_face_intersection {V : Type*} [Fintype V] [DecidableEq V]
    (K : FiniteAbstractComplex V) {s t : Finset V}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull ℝ (↑(s.image barycentricVertex) : Set (V → ℝ)) ∩
      convexHull ℝ (↑(t.image barycentricVertex) : Set (V → ℝ)) =
        convexHull ℝ (↑((s ∩ t).image barycentricVertex) : Set (V → ℝ)) := by
  rw [(realization K).convexHull_inter_convexHull
    (abstract_face_realizes K hs) (abstract_face_realizes K ht)]
  rw [barycentric_face_intersection]

/-- The underlying geometric realization is the union of the standard simplices of abstract faces.
-/
theorem realization_space_eq {V : Type*} [Fintype V] [DecidableEq V]
    (K : FiniteAbstractComplex V) :
    (realization K).space =
      ⋃ s ∈ K.faces, convexHull ℝ (↑(s.image barycentricVertex) : Set (V → ℝ)) := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hx⟩
    obtain ⟨s, hs, rfl⟩ := realized_face_originates K ht
    exact ⟨s, hs, hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s.image barycentricVertex, abstract_face_realizes K hs, hx⟩

/-- Every finite standard realization is compact. -/
theorem realization_isCompact {V : Type*} [Fintype V] [DecidableEq V]
    (K : FiniteAbstractComplex V) : IsCompact (realization K).space := by
  rw [realization_space_eq]
  exact (Set.toFinite (K.faces : Set (Finset V))).isCompact_biUnion fun s hs =>
    (s.image barycentricVertex).finite_toSet.isCompact_convexHull ℝ

end PoincareConjecture.ParallelImplementation.FinitePLRealization

#print axioms PoincareConjecture.ParallelImplementation.FinitePLRealization.abstract_face_realizes
#print axioms PoincareConjecture.ParallelImplementation.FinitePLRealization.abstractLink
#print axioms PoincareConjecture.ParallelImplementation.FinitePLRealization.realization
#print axioms PoincareConjecture.ParallelImplementation.FinitePLRealization.convexHull_abstract_face_intersection
#print axioms PoincareConjecture.ParallelImplementation.FinitePLRealization.realization_isCompact
