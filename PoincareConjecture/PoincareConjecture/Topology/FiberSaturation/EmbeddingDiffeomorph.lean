import PoincareConjecture.Topology.FiberSaturation.SmoothEmbeddingModels

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Manifold
open scoped Manifold ContDiff

variable {E F V H G W M P N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace W]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace G P]
  [TopologicalSpace N] [ChartedSpace W N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {K : ModelWithCorners ℝ V W} {f : M → N} {g : P → N}

/-- A comparison homeomorphism between two embedded parametrizations is smooth
in both directions. All three pre-existing charted structures are retained. -/
def diffeomorphOfEmbeddingComparison (hf : IsSmoothEmbedding I K ∞ f)
    (hg : IsSmoothEmbedding J K ∞ g) (e : M ≃ₜ P)
    (he : ∀ x, g (e x) = f x) : M ≃ₘ⟮I, J⟯ P where
  toEquiv := e.toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.iff_comp_isImmersion hg.isImmersion).mpr
    refine ⟨e.continuous, ?_⟩
    have hcomp : g ∘ e = f := funext he
    exact hcomp.symm ▸ hf.contMDiff
  contMDiff_invFun := by
    apply (ContMDiff.iff_comp_isImmersion hf.isImmersion).mpr
    refine ⟨e.symm.continuous, ?_⟩
    have hcomp : f ∘ e.symm = g := by
      funext y
      simpa only [Function.comp_apply, e.apply_symm_apply] using (he (e.symm y)).symm
    exact hcomp.symm ▸ hg.contMDiff

/-- The upgrade keeps the comparison map, rather than changing smooth structures. -/
@[simp] theorem diffeomorphOfEmbeddingComparison_apply
    (hf : IsSmoothEmbedding I K ∞ f) (hg : IsSmoothEmbedding J K ∞ g)
    (e : M ≃ₜ P) (he : ∀ x, g (e x) = f x) (x : M) :
    diffeomorphOfEmbeddingComparison hf hg e he x = e x := rfl

/-- Canonical identification for two smooth embeddings with exactly the same image. -/
def diffeomorphOfEqualEmbeddingRange (hf : IsSmoothEmbedding I K ∞ f)
    (hg : IsSmoothEmbedding J K ∞ g) (hrange : range f = range g) : M ≃ₘ⟮I, J⟯ P := by
  let e : M ≃ₜ P := hf.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr hrange).trans hg.isEmbedding.toHomeomorph.symm)
  apply diffeomorphOfEmbeddingComparison hf hg e
  intro x
  have h := hg.isEmbedding.toHomeomorph.apply_symm_apply
    ((Homeomorph.setCongr hrange) (hf.isEmbedding.toHomeomorph x))
  exact congrArg Subtype.val h

end PoincareConjecture.Topology.FiberSaturation
