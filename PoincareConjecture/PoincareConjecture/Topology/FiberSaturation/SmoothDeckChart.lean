import PoincareConjecture.Topology.FiberSaturation.SmoothSpliceTail
import PoincareConjecture.Topology.FiberSaturation.SmoothInterval

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Bundle Manifold
open scoped Manifold ContDiff
variable {V W H G M F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace F] [ChartedSpace G F]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G} {p : M → ℝ}

/-- The base formula for the inverse of a given smooth deck transformation. -/
theorem deck_inverse_base (T : M ≃ₘ⟮I, I⟯ M) {L : ℝ}
    (hT : ∀ z, p (T z) = p z + L) (z : M) : p (T.symm z) = p z-L := by
  have h := hT (T.symm z)
  rw [T.apply_symm_apply] at h
  linarith

/-- Transport a real-base chart by an actual smooth deck transformation. -/
def deckTranslate (e : Trivialization F p) (T : M ≃ₘ⟮I, I⟯ M)
    {L : ℝ} (hT : ∀ z, p (T z) = p z + L) : Trivialization F p := by
  let f := (e.compHomeomorph T.symm.toHomeomorph).homeomorphComp (Homeomorph.addRight L)
  have hp' : (Homeomorph.addRight L) ∘ (p ∘ T.symm.toHomeomorph) = p := by
    funext z
    change p (T.symm z)+L = p z
    rw [deck_inverse_base T hT]
    ring
  exact {
    toOpenPartialHomeomorph := f.toOpenPartialHomeomorph
    baseSet := f.baseSet
    open_baseSet := f.open_baseSet
    source_eq := f.source_eq.trans (congrArg (fun h : M → ℝ => h ⁻¹' f.baseSet) hp')
    target_eq := f.target_eq
    proj_toFun := fun z hz => (f.proj_toFun z hz).trans (congrFun hp' z) }

@[simp] theorem deckTranslate_baseSet (e : Trivialization F p) (T : M ≃ₘ⟮I,I⟯ M)
    {L : ℝ} (hT : ∀ z, p (T z) = p z+L) :
    (deckTranslate e T hT).baseSet = (fun t : ℝ => t-L) ⁻¹' e.baseSet := rfl

@[simp] theorem deckTranslate_apply (e : Trivialization F p) (T : M ≃ₘ⟮I,I⟯ M)
    {L : ℝ} (hT : ∀ z, p (T z) = p z+L) (z : M) :
    deckTranslate e T hT z = ((e (T.symm z)).1+L, (e (T.symm z)).2) := rfl

/-- Translating by a smooth deck map preserves both directions of chart smoothness. -/
theorem deckTranslate_smooth {e : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (T : M ≃ₘ⟮I,I⟯ M)
    {L : ℝ} (hT : ∀ z, p (T z) = p z+L) :
    IsSmoothTrivialization I J (deckTranslate e T hT) := by
  let g := (realTranslation L).prodCongr (Diffeomorph.refl J F ∞)
  constructor
  · have hc := he.1.comp T.symm.contMDiff.contMDiffOn (s := (deckTranslate e T hT).source)
      (by
        intro z hz
        apply e.mem_source.mpr
        rw [deck_inverse_base T hT]
        exact (deckTranslate e T hT).mem_source.mp hz)
    exact g.contMDiff.comp_contMDiffOn hc
  · have hc := he.2.comp g.symm.contMDiff.contMDiffOn (s := (deckTranslate e T hT).target)
      (by
        intro z hz
        apply e.mem_target.mpr
        exact (deckTranslate e T hT).mem_target.mp hz)
    exact T.contMDiff.comp_contMDiffOn hc

/-- The transported chart records one deck step by translating only its first coordinate. -/
theorem deckTranslate_deck_apply (e : Trivialization F p) (T : M ≃ₘ⟮I,I⟯ M)
    {L : ℝ} (hT : ∀ z, p (T z) = p z+L) (z : M) :
    deckTranslate e T hT (T z) = ((e z).1+L,(e z).2) := by
  rw [deckTranslate_apply, T.symm_apply_apply]

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
