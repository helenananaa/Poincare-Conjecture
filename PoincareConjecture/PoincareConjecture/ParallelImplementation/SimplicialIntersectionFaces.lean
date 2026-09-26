import PoincareConjecture.ParallelImplementation.SimplexExposedSubfaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SimplicialIntersectionFaces
/-- Intersections of cells from two actual geometric simplicial complexes
meet along exposed faces, as required for a common polytopal refinement. -/
theorem intersection_cells_have_exposed_intersections
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E)
    (s s' t t' : Finset E) (hs : s ∈ K.faces) (hs' : s' ∈ K.faces)
    (ht : t ∈ L.faces) (ht' : t' ∈ L.faces) :
    let C := convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)
    let D := convexHull ℝ (s' : Set E) ∩ convexHull ℝ (t' : Set E)
    IsExposed ℝ C (C ∩ D) ∧ IsExposed ℝ D (C ∩ D) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let A : Set E := convexHull ℝ (s : Set E)
  let A' : Set E := convexHull ℝ (s' : Set E)
  let B : Set E := convexHull ℝ (t : Set E)
  let B' : Set E := convexHull ℝ (t' : Set E)
  let U : Set E := convexHull ℝ ((s ∩ s' : Finset E) : Set E)
  let V : Set E := convexHull ℝ ((t ∩ t' : Finset E) : Set E)
  let C : Set E := A ∩ B
  let D : Set E := A' ∩ B'

  have hAA' : A ∩ A' = U := by
    dsimp [A, A', U]
    rw [Finset.coe_inter]
    exact K.convexHull_inter_convexHull hs hs'
  have hBB' : B ∩ B' = V := by
    dsimp [B, B', V]
    rw [Finset.coe_inter]
    exact L.convexHull_inter_convexHull ht ht'

  have exposeSubface
      {X F Y : Set E} (hXF : IsExposed ℝ X F) (hYX : Y ⊆ X) :
      IsExposed ℝ Y (Y ∩ F) := by
    by_cases hne : (Y ∩ F).Nonempty
    · intro _
      obtain ⟨x, hxY, hxF⟩ := hne
      obtain ⟨l, hl⟩ := hXF ⟨x, hxF⟩
      have hxFset := hxF
      rw [hl] at hxFset
      rcases hxFset with ⟨hxX, hmax⟩
      refine ⟨l, ?_⟩
      ext z
      rw [hl]
      constructor
      · rintro ⟨hzY, hzX, hmax⟩
        exact ⟨hzY, fun y hy => hmax y (hYX hy)⟩
      · rintro ⟨hzY, hmaxY⟩
        have hxz : l x ≤ l z := hmaxY x hxY
        have hzx : l z ≤ l x := hmax z (hYX hzY)
        have heq : l x = l z := le_antisymm hxz hzx
        refine ⟨hzY, hYX hzY, fun y hy => ?_⟩
        calc
          l y ≤ l x := hmax y hy
          _ = l z := heq
    · have hempty : Y ∩ F = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      exact isExposed_empty

  have hAU : IsExposed ℝ A U := by
    exact PoincareConjecture.ParallelImplementation.SimplexExposedSubfaces.simplex_vertex_subface_isExposed
      s (K.indep hs) (s ∩ s') Finset.inter_subset_left
  have hA'U : IsExposed ℝ A' U := by
    exact PoincareConjecture.ParallelImplementation.SimplexExposedSubfaces.simplex_vertex_subface_isExposed
      s' (K.indep hs') (s ∩ s') Finset.inter_subset_right
  have hBV : IsExposed ℝ B V := by
    exact PoincareConjecture.ParallelImplementation.SimplexExposedSubfaces.simplex_vertex_subface_isExposed
      t (L.indep ht) (t ∩ t') Finset.inter_subset_left
  have hB'V : IsExposed ℝ B' V := by
    exact PoincareConjecture.ParallelImplementation.SimplexExposedSubfaces.simplex_vertex_subface_isExposed
      t' (L.indep ht') (t ∩ t') Finset.inter_subset_right

  have hCU : IsExposed ℝ C (C ∩ U) :=
    exposeSubface hAU (by dsimp [C]; exact Set.inter_subset_left)
  have hCV : IsExposed ℝ C (C ∩ V) :=
    exposeSubface hBV (by dsimp [C]; exact Set.inter_subset_right)
  have hDU : IsExposed ℝ D (D ∩ U) :=
    exposeSubface hA'U (by dsimp [D]; exact Set.inter_subset_left)
  have hDV : IsExposed ℝ D (D ∩ V) :=
    exposeSubface hB'V (by dsimp [D]; exact Set.inter_subset_right)

  have hCtarget : C ∩ D = (C ∩ U) ∩ (C ∩ V) := by
    ext x
    change (x ∈ A ∩ B ∧ x ∈ A' ∩ B') ↔
      (x ∈ (A ∩ B) ∩ U ∧ x ∈ (A ∩ B) ∩ V)
    constructor
    · rintro ⟨⟨hxA, hxB⟩, ⟨hxA', hxB'⟩⟩
      have hxU : x ∈ U := by rw [← hAA']; exact ⟨hxA, hxA'⟩
      have hxV : x ∈ V := by rw [← hBB']; exact ⟨hxB, hxB'⟩
      exact ⟨⟨⟨hxA, hxB⟩, hxU⟩, ⟨⟨hxA, hxB⟩, hxV⟩⟩
    · rintro ⟨⟨⟨hxA, hxB⟩, hxU⟩, ⟨_, hxV⟩⟩
      have hxAA' : x ∈ A ∩ A' := by rw [hAA']; exact hxU
      have hxBB' : x ∈ B ∩ B' := by rw [hBB']; exact hxV
      exact ⟨⟨hxA, hxB⟩, ⟨hxAA'.2, hxBB'.2⟩⟩

  have hDtarget : C ∩ D = (D ∩ U) ∩ (D ∩ V) := by
    ext x
    change (x ∈ A ∩ B ∧ x ∈ A' ∩ B') ↔
      (x ∈ (A' ∩ B') ∩ U ∧ x ∈ (A' ∩ B') ∩ V)
    constructor
    · rintro ⟨⟨hxA, hxB⟩, ⟨hxA', hxB'⟩⟩
      have hxU : x ∈ U := by rw [← hAA']; exact ⟨hxA, hxA'⟩
      have hxV : x ∈ V := by rw [← hBB']; exact ⟨hxB, hxB'⟩
      exact ⟨⟨⟨hxA', hxB'⟩, hxU⟩, ⟨⟨hxA', hxB'⟩, hxV⟩⟩
    · rintro ⟨⟨⟨hxA', hxB'⟩, hxU⟩, ⟨_, hxV⟩⟩
      have hxAA' : x ∈ A ∩ A' := by rw [hAA']; exact hxU
      have hxBB' : x ∈ B ∩ B' := by rw [hBB']; exact hxV
      exact ⟨⟨hxAA'.1, hxBB'.1⟩, ⟨hxA', hxB'⟩⟩

  constructor
  · change IsExposed ℝ C (C ∩ D)
    rw [hCtarget]
    exact hCU.inter hCV
  · change IsExposed ℝ D (C ∩ D)
    rw [hDtarget]
    exact hDU.inter hDV
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SimplicialIntersectionFaces
