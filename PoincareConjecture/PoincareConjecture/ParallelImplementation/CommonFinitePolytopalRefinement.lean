import PoincareConjecture.ParallelImplementation.FinitePolytopeExposedTransitivity
import PoincareConjecture.ParallelImplementation.FiniteSimplexIntersection
import PoincareConjecture.ParallelImplementation.FinitePolytopeExposedFaces
import PoincareConjecture.ParallelImplementation.SimplicialIntersectionFaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CommonFinitePolytopalRefinement
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def commonFaceFamily (K L : Geometry.SimplicialComplex ℝ E) : Set (Set E) :=
  {F | ∃ s ∈ K.faces, ∃ t ∈ L.faces,
    IsExposed ℝ (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)) F}
/-- The actual intersections of two finite geometric complexes and ALL their
exposed faces form a finite polytopal refinement in the original ambient space.
No finite face family or intersection compatibility is assumed. -/
theorem actual_finite_common_polytopal_refinement [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hL : L.faces.Finite) :
    (commonFaceFamily K L).Finite ∧
    (∀ F ∈ commonFaceFamily K L, ∃ s : Finset E, F = convexHull ℝ (s : Set E)) ∧
    (∀ F ∈ commonFaceFamily K L, ∀ G : Set E,
      IsExposed ℝ F G → G ∈ commonFaceFamily K L) ∧
    (∀ F ∈ commonFaceFamily K L, ∀ G ∈ commonFaceFamily K L,
      IsExposed ℝ F (F ∩ G) ∧ IsExposed ℝ G (F ∩ G)) ∧
    ⋃₀ commonFaceFamily K L = K.space ∩ L.space ∧
    (∀ F ∈ commonFaceFamily K L, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
      F ⊆ convexHull ℝ (s : Set E) ∧ F ⊆ convexHull ℝ (t : Set E)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let cellIntersection (s t : Finset E) :=
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)

  have intersection_hull (s : Finset E) (t : Finset E)
      (hs : s ∈ K.faces) (ht : t ∈ L.faces) :
    ∃ r : Finset E, cellIntersection s t = convexHull ℝ (r : Set E) := by
    obtain ⟨r, hr, _⟩ :=
      PoincareConjecture.ParallelImplementation.FiniteSimplexIntersection.exists_finite_vertices_convexHull_inter_simplex s t
        (L.nonempty_of_mem_faces ht) (L.indep ht)
    exact ⟨r, by simpa [cellIntersection] using hr⟩

  have family_eq_biUnion : commonFaceFamily K L =
      ⋃ s ∈ K.faces, ⋃ t ∈ L.faces, {F : Set E | IsExposed ℝ (cellIntersection s t) F} := by
    ext F
    simp [commonFaceFamily, cellIntersection]

  have pairFamily_finite (s t : Finset E) (hs : s ∈ K.faces) (ht : t ∈ L.faces) :
      {F : Set E | IsExposed ℝ (cellIntersection s t) F}.Finite := by
    obtain ⟨r, hr⟩ := intersection_hull s t hs ht
    rw [hr]
    exact (PoincareConjecture.ParallelImplementation.FinitePolytopeExposedFaces.exposed_faces_are_finitely_generated r).2

  have hfinite : (commonFaceFamily K L).Finite := by
    rw [family_eq_biUnion]
    apply hK.biUnion
    intro s hs
    apply hL.biUnion
    intro t ht
    exact pairFamily_finite s t hs ht

  have face_hull (F : Set E) (hF : F ∈ commonFaceFamily K L) :
      ∃ r : Finset E, F = convexHull ℝ (r : Set E) := by
    change ∃ s ∈ K.faces, ∃ t ∈ L.faces, IsExposed ℝ (cellIntersection s t) F at hF
    obtain ⟨s, hs, t, ht, hExp⟩ := hF
    obtain ⟨r, hr⟩ := intersection_hull s t hs ht
    have hExp' : IsExposed ℝ (convexHull ℝ (r : Set E)) F := by
      rw [← hr]
      exact hExp
    obtain ⟨u, _, hu⟩ :=
      (PoincareConjecture.ParallelImplementation.FinitePolytopeExposedFaces.exposed_faces_are_finitely_generated r).1 F hExp'
    exact ⟨u, hu⟩

  have restrict_exposed {X Y Z : Set E} (hXY : IsExposed ℝ X Y)
      (hZX : Z ⊆ X) : IsExposed ℝ Z (Z ∩ Y) := by
    by_cases hne : (Z ∩ Y).Nonempty
    · obtain ⟨x, hxZ, hxY⟩ := hne
      intro _
      obtain ⟨l, hl⟩ := hXY ⟨x, hxY⟩
      have hxMax : x ∈ {z ∈ X | ∀ y ∈ X, l y ≤ l z} := by
        rw [← hl]
        exact hxY
      rcases hxMax with ⟨hxX, hxMax⟩
      refine ⟨l, ?_⟩
      ext z
      rw [hl]
      constructor
      · rintro ⟨hzZ, ⟨_, hzMax⟩⟩
        exact ⟨hzZ, fun y hy => hzMax y (hZX hy)⟩
      · rintro ⟨hzZ, hzMax⟩
        have hxz : l x ≤ l z := hzMax x hxZ
        refine ⟨hzZ, ⟨hZX hzZ, ?_⟩⟩
        intro y hy
        exact (hxMax y hy).trans hxz
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact isExposed_empty

  refine ⟨hfinite, ?_, ?_, ?_, ?_, ?_⟩
  · intro F hF
    exact face_hull F hF
  · intro F hF G hG
    change ∃ s ∈ K.faces, ∃ t ∈ L.faces, IsExposed ℝ (cellIntersection s t) F at hF
    obtain ⟨s, hs, t, ht, hExp⟩ := hF
    obtain ⟨r, hr⟩ := intersection_hull s t hs ht
    have hExp' : IsExposed ℝ (convexHull ℝ (r : Set E)) F := by
      rw [← hr]
      exact hExp
    have hG' : IsExposed ℝ F G := hG
    have hTrans :=
      PoincareConjecture.ParallelImplementation.FinitePolytopeExposedTransitivity.exposed_face_transitive_of_finite_hull r F G hExp' hG'
    refine ⟨s, hs, t, ht, ?_⟩
    rw [← hr] at hTrans
    exact hTrans
  · intro F hF G hG
    obtain ⟨u, hFset⟩ := face_hull F hF
    obtain ⟨v, hGset⟩ := face_hull G hG
    change ∃ s ∈ K.faces, ∃ t ∈ L.faces, IsExposed ℝ (cellIntersection s t) F at hF
    change ∃ s' ∈ K.faces, ∃ t' ∈ L.faces, IsExposed ℝ (cellIntersection s' t') G at hG
    obtain ⟨s, hs, t, ht, hFbase⟩ := hF
    obtain ⟨s', hs', t', ht', hGbase⟩ := hG
    let I := cellIntersection s t
    let J := cellIntersection s' t'
    have hFI : IsExposed ℝ I F := hFbase
    have hGJ : IsExposed ℝ J G := hGbase
    have hIJ :=
      PoincareConjecture.ParallelImplementation.SimplicialIntersectionFaces.intersection_cells_have_exposed_intersections K L s s' t t' hs hs' ht ht'
    have hFIJ : IsExposed ℝ F (F ∩ (I ∩ J)) := by
      exact restrict_exposed hIJ.1 hFI.subset
    let X := F ∩ (I ∩ J)
    have hXJ : X ⊆ J := by
      intro x hx
      exact hx.2.2
    have hXG : IsExposed ℝ X (X ∩ G) := by
      exact restrict_exposed hGJ hXJ
    have hFIJ' : IsExposed ℝ (convexHull ℝ (u : Set E)) X := by
      simpa [X, hFset] using hFIJ
    have hHullXG : IsExposed ℝ (convexHull ℝ (u : Set E)) (X ∩ G) :=
      PoincareConjecture.ParallelImplementation.FinitePolytopeExposedTransitivity.exposed_face_transitive_of_finite_hull u X (X ∩ G) hFIJ' hXG
    have hXG_eq : X ∩ G = F ∩ G := by
      ext x
      constructor
      · rintro ⟨⟨hxF, _⟩, hxG⟩
        exact ⟨hxF, hxG⟩
      · rintro ⟨hxF, hxG⟩
        have hxI : x ∈ I := hFI.subset hxF
        exact ⟨⟨hxF, ⟨hxI, hGJ.subset hxG⟩⟩, hxG⟩
    have hFmeetG : IsExposed ℝ F (F ∩ G) := by
      have hXG_eq' : X ∩ G = convexHull ℝ (u : Set E) ∩ G := by
        simpa [X, hFset] using hXG_eq
      rw [hFset, ← hXG_eq']
      exact hHullXG

    have hJGI : IsExposed ℝ J (J ∩ I) := by
      simpa [I, J, cellIntersection, Set.inter_comm] using hIJ.2
    have hGJI : IsExposed ℝ G (G ∩ (J ∩ I)) := by
      exact restrict_exposed hJGI hGJ.subset
    let Y := G ∩ (J ∩ I)
    have hYI : Y ⊆ I := by
      intro x hx
      exact hx.2.2
    have hYF : IsExposed ℝ Y (Y ∩ F) := by
      exact restrict_exposed hFI hYI
    have hGJI' : IsExposed ℝ (convexHull ℝ (v : Set E)) Y := by
      simpa [Y, hGset] using hGJI
    have hHullYF : IsExposed ℝ (convexHull ℝ (v : Set E)) (Y ∩ F) :=
      PoincareConjecture.ParallelImplementation.FinitePolytopeExposedTransitivity.exposed_face_transitive_of_finite_hull v Y (Y ∩ F) hGJI' hYF
    have hYF_eq : Y ∩ F = G ∩ F := by
      ext x
      constructor
      · rintro ⟨⟨hxG, _⟩, hxF⟩
        exact ⟨hxG, hxF⟩
      · rintro ⟨hxG, hxF⟩
        have hxJ : x ∈ J := hGJ.subset hxG
        exact ⟨⟨hxG, ⟨hxJ, hFI.subset hxF⟩⟩, hxF⟩
    have hGmeetF : IsExposed ℝ G (F ∩ G) := by
      have hYF_eq' : Y ∩ F = convexHull ℝ (v : Set E) ∩ F := by
        simpa [Y, hGset] using hYF_eq
      have hGmeetF' : IsExposed ℝ (convexHull ℝ (v : Set E))
          (convexHull ℝ (v : Set E) ∩ F) := by
        rw [← hYF_eq']
        exact hHullYF
      rw [Set.inter_comm, hGset]
      exact hGmeetF'
    exact ⟨hFmeetG, hGmeetF⟩
  · apply Set.ext
    intro x
    constructor
    · intro hx
      rcases Set.mem_sUnion.mp hx with ⟨F, hF, hxF⟩
      change ∃ s ∈ K.faces, ∃ t ∈ L.faces,
        IsExposed ℝ (cellIntersection s t) F at hF
      obtain ⟨s, hs, t, ht, hExp⟩ := hF
      have hxI : x ∈ cellIntersection s t := hExp.subset hxF
      rcases hxI with ⟨hxs, hxt⟩
      refine ⟨?_, ?_⟩
      · apply K.mem_space_iff.mpr
        exact ⟨s, hs, hxs⟩
      · apply L.mem_space_iff.mpr
        exact ⟨t, ht, hxt⟩
    · rintro ⟨hxK, hxL⟩
      rcases K.mem_space_iff.mp hxK with ⟨s, hs, hxs⟩
      rcases L.mem_space_iff.mp hxL with ⟨t, ht, hxt⟩
      apply Set.mem_sUnion.mpr
      refine ⟨cellIntersection s t, ?_, ⟨hxs, hxt⟩⟩
      exact ⟨s, hs, t, ht, IsExposed.refl _⟩
  · intro F hF
    change ∃ s ∈ K.faces, ∃ t ∈ L.faces, IsExposed ℝ (cellIntersection s t) F at hF
    obtain ⟨s, hs, t, ht, hExp⟩ := hF
    refine ⟨s, hs, t, ht, ?_, ?_⟩
    · exact hExp.subset.trans Set.inter_subset_left
    · exact hExp.subset.trans Set.inter_subset_right
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CommonFinitePolytopalRefinement
