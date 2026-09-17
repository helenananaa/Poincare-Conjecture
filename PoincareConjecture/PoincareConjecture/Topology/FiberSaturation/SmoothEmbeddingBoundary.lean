import PoincareConjecture.Topology.FiberSaturation.MaximalAtlasBoundary
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.Topology.FiberSaturation
open Set Function Manifold
open scoped Manifold ContDiff

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [J.Boundaryless] [IsManifold I ∞ M]

/-- No additional ambient-chart input: it is constructed from the embedding. -/
theorem smoothEmbedding_interior_iff {f : M → N}
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (x : M) :
    I.IsInteriorPoint x ↔ f x ∈ interior (range f) := by
  obtain ⟨a, e, ha, hx, he, hs, hp⟩ := exists_codimensionZero_ambient_chart hf hdim x
  rw [intrinsicInterior_iff_maximalChart (by simp : (∞ : ℕ∞ω) ≠ 0) ha hx, ← hp]
  exact hs.interior he

/-- Intrinsic boundary is the ambient frontier at every image point. -/
theorem smoothEmbedding_boundary_iff {f : M → N}
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (x : M) :
    I.IsBoundaryPoint x ↔ f x ∈ frontier (range f) := by
  obtain ⟨a, e, ha, hx, he, hs, hp⟩ := exists_codimensionZero_ambient_chart hf hdim x
  rw [intrinsicBoundary_iff_maximalChart (by simp : (∞ : ℕ∞ω) ≠ 0) ha hx, ← hp]
  exact hs.frontier he

/-- Image of the intrinsic interior, with no properness assumption. -/
theorem smoothEmbedding_interior_image {f : M → N}
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    f '' I.interior M = interior (range f) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (smoothEmbedding_interior_iff hf hdim x).mp hx
  · intro hy
    obtain ⟨x, rfl⟩ := interior_subset hy
    exact ⟨x, (smoothEmbedding_interior_iff hf hdim x).mpr hy, rfl⟩

/-- Closed image ensures there are no additional frontier limit points. -/
theorem smoothEmbedding_boundary_image {f : M → N}
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hclosed : IsClosed (range f)) :
    f '' I.boundary M = frontier (range f) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (smoothEmbedding_boundary_iff hf hdim x).mp hx
  · intro hy
    obtain ⟨x, rfl⟩ := hclosed.closure_eq ▸ hy.1
    exact ⟨x, (smoothEmbedding_boundary_iff hf hdim x).mpr hy, rfl⟩

/-- Properness supplies the closed-image condition; it is not an assumed boundary equality. -/
theorem proper_smoothEmbedding_boundary_image [T1Space N] {f : M → N}
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hp : IsProperMap f) :
    f '' I.boundary M = frontier (range f) :=
  smoothEmbedding_boundary_image hf hdim hp.isClosed_range

end PoincareConjecture.Topology.FiberSaturation
