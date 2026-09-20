import LeeSmoothLib.Verified.LevelSets.EmbeddingTransport
import LeeSmoothLib.Verified.LevelSets.RegularValue
import LeeSmoothLib.Verified.LevelSets.ConstantRank

open scoped Manifold ContDiff
open Manifold Set
noncomputable section
namespace LeeVerifiedLevelSets.Generic
open ModelTransport

variable {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

private lemma rechart_fiber_image (f : M → N) (c : N) :
    EuclideanRechart.val '' ((rechartMap f) ⁻¹' {EuclideanRechart.mk c}) = f ⁻¹' {c} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact congrArg EuclideanRechart.val hy
  · intro hx
    exact ⟨⟨x⟩, congrArg EuclideanRechart.mk hx, rfl⟩
/-- The C∞ regular-level theorem in arbitrary finite-dimensional boundaryless real models. -/
theorem regular_level_set_smooth_structure {f : M → N} {c : N}
    (hf : ContMDiff I J ∞ f) (hc : IsRegularValue I J f c)
    (hnm : Module.finrank ℝ E' ≤ Module.finrank ℝ E) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ E')))
        (f ⁻¹' {c}),
      ∃ hs : IsManifold (𝓡 (Module.finrank ℝ E - Module.finrank ℝ E')) ∞ (f ⁻¹' {c}),
        letI := cs
        letI := hs
        IsSmoothEmbedding (𝓡 (Module.finrank ℝ E - Module.finrank ℝ E')) I ∞
          (Subtype.val : f ⁻¹' {c} → M) := by
  letI := euclideanRechartChartedSpace (I := I) (M := M)
  letI := euclideanRechartChartedSpace (I := J) (M := N)
  letI := euclideanRechart_isManifold (I := I) (M := M)
  letI := euclideanRechart_isManifold (I := J) (M := N)
  obtain ⟨cs, hs, hemb⟩ :=
    LeeVerifiedLevelSets.regular_level_set_has_embedded_submanifold_structure
      (contMDiff_rechartMap hf) (isRegularValue_rechartMap hf hc) hnm
  letI := cs
  letI := hs
  have hpack := EmbeddingTransport.image_has_smooth_embedded_structure
    (euclideanRechartDiffeomorph (I := I) (M := M))
    ((rechartMap f) ⁻¹' {EuclideanRechart.mk c}) hemb
  have heq : (euclideanRechartDiffeomorph (I := I) (M := M) : EuclideanRechart M → M) =
      EuclideanRechart.val := rfl
  rwa [heq, rechart_fiber_image] at hpack

/-- Constant-rank fibres inherit a C∞ structure without changing the original ambient atlas. -/
theorem constant_rank_level_set_smooth_structure_of_le {f : M → N} {r : ℕ}
    (hf : ContMDiff I J ∞ f) (hr : HasConstantRank I J f r) (c : N)
    (hrm : r ≤ Module.finrank ℝ E) (hrn : r ≤ Module.finrank ℝ E') :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) (f ⁻¹' {c}),
      ∃ hs : IsManifold (𝓡 (Module.finrank ℝ E - r)) ∞ (f ⁻¹' {c}),
        letI := cs
        letI := hs
        IsSmoothEmbedding (𝓡 (Module.finrank ℝ E - r)) I ∞
          (Subtype.val : f ⁻¹' {c} → M) := by
  letI := euclideanRechartChartedSpace (I := I) (M := M)
  letI := euclideanRechartChartedSpace (I := J) (M := N)
  letI := euclideanRechart_isManifold (I := I) (M := M)
  letI := euclideanRechart_isManifold (I := J) (M := N)
  obtain ⟨cs, hs, hemb⟩ :=
    LeeVerifiedLevelSets.constant_rank_level_set_has_embedded_submanifold_structure
      (contMDiff_rechartMap hf) (hasConstantRank_rechartMap hf hr)
      (EuclideanRechart.mk c) hrm hrn
  letI := cs
  letI := hs
  have hpack := EmbeddingTransport.image_has_smooth_embedded_structure
    (euclideanRechartDiffeomorph (I := I) (M := M))
    ((rechartMap f) ⁻¹' {EuclideanRechart.mk c}) hemb
  have heq : (euclideanRechartDiffeomorph (I := I) (M := M) : EuclideanRechart M → M) =
      EuclideanRechart.val := rfl
  rwa [heq, rechart_fiber_image] at hpack

/-- Only the source codimension bound is needed; an empty fibre causes no target-rank constraint. -/
theorem constant_rank_level_set_smooth_structure {f : M → N} {r : ℕ}
    (hf : ContMDiff I J ∞ f) (hr : HasConstantRank I J f r) (c : N)
    (hrm : r ≤ Module.finrank ℝ E) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) (f ⁻¹' {c}),
      ∃ hs : IsManifold (𝓡 (Module.finrank ℝ E - r)) ∞ (f ⁻¹' {c}),
        letI := cs
        letI := hs
        IsSmoothEmbedding (𝓡 (Module.finrank ℝ E - r)) I ∞
          (Subtype.val : f ⁻¹' {c} → M) := by
  by_cases hempty : (f ⁻¹' {c}) = ∅
  · rw [hempty]
    let cs : ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))) (∅ : Set M) :=
      ChartedSpace.empty _ _
    refine ⟨cs, ?_⟩
    letI := cs
    let hs : IsManifold (𝓡 (Module.finrank ℝ E - r)) ∞ (∅ : Set M) := inferInstance
    exact ⟨hs, ⟨⟨PUnit, inferInstance, inferInstance, fun x => False.elim x.2⟩,
      Topology.IsEmbedding.subtypeVal⟩⟩
  · obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    let A : E →L[ℝ] E' := mfderiv I J f p
    have hAr : Module.finrank ℝ A.range = r := hr.2 p
    have hrn : r ≤ Module.finrank ℝ E' := hAr.symm.trans_le (Submodule.finrank_le A.range)
    exact constant_rank_level_set_smooth_structure_of_le hf hr c hrm hrn

end LeeVerifiedLevelSets.Generic
end
