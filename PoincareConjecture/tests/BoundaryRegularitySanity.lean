import PoincareConjecture

open Set PoincareConjecture.Topology.FiberSaturation

-- A genuine three-dimensional half-space supplies the new local chart witnesses.
example : HasAmbientModelCharts (modelWithCornersEuclideanHalfSpace 3) (closedHalfSpace 3) :=
  closedHalfSpace_hasAmbientModelCharts 3

-- The intrinsic manifold boundary is the actual coordinate plane.
example : (Subtype.val : closedHalfSpace 3 → EuclideanSpace ℝ (Fin 3)) ''
    (modelWithCornersEuclideanHalfSpace 3).boundary (closedHalfSpace 3) =
      {x | x 0 = 0} := closedHalfSpace_boundary_image 3

-- The intrinsic interior is the strict half-space, not the whole closed set.
example : (Subtype.val : closedHalfSpace 3 → EuclideanSpace ℝ (Fin 3)) ''
    (modelWithCornersEuclideanHalfSpace 3).interior (closedHalfSpace 3) =
      {x | 0 < x 0} := by
  rw [intrinsicInterior_image_eq (closedHalfSpace_hasAmbientModelCharts 3)]
  exact interior_halfSpace 2 0 (0 : Fin 3)

-- The open-domain bridge recovers the usual interval without adding regularity.
example : Ioo (0 : ℝ) 1 = interior (closure (Ioo (0 : ℝ) 1)) := by
  apply regularOpen_of_frontier_closure_eq isOpen_Ioo
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
    frontier_Icc, frontier_Ioo (by norm_num : (0 : ℝ) < 1)]
  norm_num

-- A punctured line shows why openness and nonempty frontier do NOT suffice.
example : let D : Set ℝ := Iio 0 ∪ Ioi 0
    (frontier D).Nonempty ∧ frontier (closure D) = ∅ ∧ D ≠ interior (closure D) := by
  dsimp
  have ho : IsOpen (Iio (0 : ℝ) ∪ Ioi 0) := isOpen_Iio.union isOpen_Ioi
  have hcl : closure (Iio (0 : ℝ) ∪ Ioi 0) = univ := by
    rw [closure_union, closure_Iio, closure_Ioi]
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total x 0
  refine ⟨⟨0, ?_⟩, ?_, ?_⟩
  · rw [ho.frontier_eq, hcl]
    simp
  · rw [hcl, frontier_univ]
  · intro h
    have hzero : (0 : ℝ) ∈ Iio 0 ∪ Ioi 0 := by
      rw [h, hcl, interior_univ]
      exact mem_univ _
    simp at hzero
