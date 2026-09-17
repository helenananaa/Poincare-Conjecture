import PoincareConjecture.Topology.FiberSaturation.BoundaryRegionAdapter
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- The actual Euclidean half-space as an ambient subset. -/
abbrev closedHalfSpace (n : ℕ) [NeZero n] : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | 0 ≤ x 0}

/-- Canonical model chart structure on the subset, not an arbitrary boundary predicate. -/
instance closedHalfSpace_chartedSpace (n : ℕ) [NeZero n] :
    ChartedSpace (EuclideanHalfSpace n) (closedHalfSpace n) :=
  inferInstanceAs (ChartedSpace (EuclideanHalfSpace n) (EuclideanHalfSpace n))

/-- The local chart-extension condition is inhabited by every actual Euclidean
half-space. The ambient chart is the identity; intrinsic charts are canonical. -/
theorem closedHalfSpace_hasAmbientModelCharts (n : ℕ) [NeZero n] :
    HasAmbientModelCharts (modelWithCornersEuclideanHalfSpace n) (closedHalfSpace n) := by
  intro p
  refine ⟨OpenPartialHomeomorph.refl _, mem_univ _, ?_, ?_⟩
  · intro x _
    change x ∈ range (modelWithCornersEuclideanHalfSpace n) ↔ 0 ≤ x 0
    rw [range_modelWithCornersEuclideanHalfSpace]
    rfl
  · change p.1 = extChartAt (modelWithCornersEuclideanHalfSpace n)
      (p : EuclideanHalfSpace n) p
    rfl

/-- Intrinsic and ambient boundaries coincide on a genuine nonempty model. -/
theorem closedHalfSpace_boundary_image (n : ℕ) [NeZero n] :
    (Subtype.val : closedHalfSpace n → EuclideanSpace ℝ (Fin n)) ''
      (modelWithCornersEuclideanHalfSpace n).boundary (closedHalfSpace n) =
        {x | x 0 = 0} := by
  rw [intrinsicBoundary_image_eq (closedHalfSpace_hasAmbientModelCharts n)
    (isClosed_le continuous_const (PiLp.continuous_apply 2 _ 0))]
  simpa only [closedHalfSpace, eq_comm] using frontier_halfSpace (n := n) 2 0 (0 : Fin n)

end PoincareConjecture.Topology.FiberSaturation
