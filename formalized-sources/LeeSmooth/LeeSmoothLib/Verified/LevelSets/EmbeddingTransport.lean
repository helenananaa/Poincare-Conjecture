import LeeSmoothLib.Verified.LevelSets.ModelTransport
import LeeSmoothLib.Ch05.Sec05_28.Proposition_5_2

open scoped ContDiff Manifold
open Set Manifold
noncomputable section
namespace LeeVerifiedLevelSets.EmbeddingTransport

variable {E E₁ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  {H H₁ : Type*} [TopologicalSpace H] [TopologicalSpace H₁]
  {I : ModelWithCorners ℝ E H} {I₁ : ModelWithCorners ℝ E₁ H₁}
  [I.Boundaryless] [I₁.Boundaryless]
  {M M₁ : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]

omit [FiniteDimensional ℝ E₁] [I₁.Boundaryless] in
/-- Transport an actual smooth embedded subset through an ambient diffeomorphism. -/
theorem image_has_smooth_embedded_structure (e : M₁ ≃ₘ⟮I₁, I⟯ M)
    {k : ℕ} (S : Set M₁)
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) S] [IsManifold (𝓡 k) ∞ S]
    (hS : IsSmoothEmbedding (𝓡 k) I₁ ∞ (Subtype.val : S → M₁)) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) (e '' S),
      ∃ hs : IsManifold (𝓡 k) ∞ (e '' S),
        letI := cs
        letI := hs
        IsSmoothEmbedding (𝓡 k) I ∞ (Subtype.val : e '' S → M) := by
  let f : S → M := e ∘ Subtype.val
  have hsmooth : ContMDiff (𝓡 k) I ∞ f := e.contMDiff.comp hS.contMDiff
  have himm : IsImmersion (𝓡 k) I ∞ f := by
    apply (is_immersion_iff_forall_injective_mfderiv hsmooth).mpr
    intro x
    have heinj : Function.Injective (mfderiv I₁ I e (x : M₁)) :=
      (e.mfderivToContinuousLinearEquiv (by simp) (x : M₁)).injective
    change Function.Injective (mfderiv (𝓡 k) I (e ∘ Subtype.val) x)
    rw [mfderiv_comp x (e.contMDiff.mdifferentiableAt (by simp))
      (hS.contMDiff.mdifferentiableAt (by simp))]
    exact heinj.comp (hS.isImmersion.mfderiv_injective x)
  have hemb : IsSmoothEmbedding (𝓡 k) I ∞ f :=
    ⟨himm, e.toHomeomorph.isEmbedding.comp hS.isEmbedding⟩
  obtain ⟨cs, hcs⟩ := smooth_embedding_range_has_induced_manifold_structure hemb
  obtain ⟨hs, hsub, _⟩ := hcs
  have hrange : range f = e '' S := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hpack : ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) (range f),
      ∃ hs : IsManifold (𝓡 k) ∞ (range f),
        letI := cs
        letI := hs
        IsSmoothEmbedding (𝓡 k) I ∞ (Subtype.val : range f → M) :=
    ⟨cs, hs, hsub⟩
  rwa [hrange] at hpack

end LeeVerifiedLevelSets.EmbeddingTransport
end
