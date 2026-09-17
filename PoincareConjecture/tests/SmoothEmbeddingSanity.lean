import PoincareConjecture.Topology.FiberSaturation.SmoothEmbeddingModels

open Set PoincareConjecture.Topology.FiberSaturation
open scoped Manifold ContDiff
noncomputable section

-- Real boundary-bearing smooth embeddings in every positive dimension.
example (n : ℕ) [NeZero n] :
    (𝓡∂ n) '' (𝓡∂ n).boundary (EuclideanHalfSpace n) =
      {v : EuclideanSpace ℝ (Fin n) | v 0 = 0} := by
  rw [smoothEmbedding_boundary_image (model_inclusion_smoothEmbedding (𝓡∂ n))
    rfl (𝓡∂ n).isClosed_range]
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  ext v
  exact eq_comm

-- The newly constructed ambient chart applies at the actual boundary point.
example : ∃ a : OpenPartialHomeomorph (EuclideanHalfSpace 3) (EuclideanHalfSpace 3),
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)),
      a ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ (EuclideanHalfSpace 3) ∧
      (0 : EuclideanHalfSpace 3) ∈ a.source ∧ (0 : EuclideanSpace ℝ (Fin 3)) ∈ e.source ∧
      e.IsImage (range (𝓡∂ 3)) (range (𝓡∂ 3)) ∧ e 0 = a.extend (𝓡∂ 3) 0 := by
  exact exists_codimensionZero_ambient_chart (model_inclusion_smoothEmbedding (𝓡∂ 3)) rfl 0

-- The interior side of the same theorem is also non-vacuous.
example (n : ℕ) [NeZero n] (p : EuclideanHalfSpace n) :
    (𝓡∂ n).IsInteriorPoint p ↔ 0 < p.1 0 := by
  rw [smoothEmbedding_interior_iff (model_inclusion_smoothEmbedding (𝓡∂ n)) rfl p,
    interior_range_modelWithCornersEuclideanHalfSpace]
  rfl

example : (𝓡∂ 3).IsBoundaryPoint (0 : EuclideanHalfSpace 3) := by
  apply (smoothEmbedding_boundary_iff (model_inclusion_smoothEmbedding (𝓡∂ 3)) rfl 0).mpr
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  simp [modelWithCornersEuclideanHalfSpace_zero]

-- Equal-dimensional zero-space models are not excluded by a positive-dimension assumption.
example : (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).boundary (EuclideanSpace ℝ (Fin 0)) = ∅ := by
  have h := smoothEmbedding_boundary_image
    (model_inclusion_smoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) rfl
    (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).isClosed_range
  simpa using h
