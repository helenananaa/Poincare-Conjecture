import PoincareConjecture.Topology.FiberSaturation.SmoothSeamClamp
import Mathlib.Topology.FiberBundle.Trivialization
import Mathlib.Geometry.Manifold.LocalDiffeomorph

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
  (I : ModelWithCorners ℝ V H) (J : ModelWithCorners ℝ W G)
  {p : M → ℝ}

/-- Smoothness of an actual bundle trivialization in the supplied structures.
Both directions are checked only on their genuine open chart domains. -/
def IsSmoothTrivialization (e : Trivialization F p) : Prop :=
  ContMDiffOn I ((𝓘(ℝ, ℝ)).prod J) ∞ e e.source ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod J) I ∞ e.toOpenPartialHomeomorph.symm e.target

variable {I J}

theorem contMDiffOn_coordChange {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod J) J ∞
      (fun z : ℝ × F => e.coordChange f z.1 z.2)
      ((e.baseSet ∩ f.baseSet) ×ˢ (univ : Set F)) := by
  have h1 := he.2.mono (show (e.baseSet ∩ f.baseSet) ×ˢ (univ : Set F) ⊆ e.target from
    fun z hz => e.mem_target.mpr hz.1.1)
  have h2 := hf.1.comp h1 (by
    intro z hz
    apply f.mem_source.mpr
    rw [e.proj_symm_apply' hz.1.1]
    exact hz.1.2)
  exact contMDiff_snd.comp_contMDiffOn h2

/-- Evaluate a smooth coordinate change at a smooth parameter without moving
base points. Fiberwise inverses give a genuine global product diffeomorphism. -/
def transitionDiffeomorph {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρmem : ∀ t, ρ t ∈ e.baseSet ∩ f.baseSet) :
    (ℝ × F) ≃ₘ⟮(𝓘(ℝ, ℝ)).prod J, (𝓘(ℝ, ℝ)).prod J⟯ (ℝ × F) where
  toFun z := (z.1, e.coordChange f (ρ z.1) z.2)
  invFun z := (z.1, f.coordChange e (ρ z.1) z.2)
  left_inv z := by simp [Trivialization.coordChange_coordChange, (hρmem z.1).1,
    (hρmem z.1).2, Trivialization.coordChange_same_apply]
  right_inv z := by simp [Trivialization.coordChange_coordChange, (hρmem z.1).1,
    (hρmem z.1).2, Trivialization.coordChange_same_apply]
  contMDiff_toFun := by
    have hparam : ContMDiff ((𝓘(ℝ, ℝ)).prod J) ((𝓘(ℝ, ℝ)).prod J) ∞
        (fun z : ℝ × F => (ρ z.1, z.2)) :=
      (hρ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    exact contMDiff_fst.prodMk ((contMDiffOn_coordChange he hf).comp_contMDiff
      hparam (fun z => ⟨hρmem z.1, mem_univ _⟩))
  contMDiff_invFun := by
    have hparam : ContMDiff ((𝓘(ℝ, ℝ)).prod J) ((𝓘(ℝ, ℝ)).prod J) ∞
        (fun z : ℝ × F => (ρ z.1, z.2)) :=
      (hρ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    exact contMDiff_fst.prodMk ((contMDiffOn_coordChange hf he).comp_contMDiff
      hparam (fun z => ⟨⟨(hρmem z.1).2,(hρmem z.1).1⟩, mem_univ _⟩))


/-- Restricting the base to an open set preserves both smooth chart maps. -/
theorem isSmooth_restrOpen {e : Trivialization F p} (he : IsSmoothTrivialization I J e)
    (A : Set ℝ) (hA : IsOpen A) : IsSmoothTrivialization I J (e.restrOpen A hA) := by
  constructor
  · exact he.1.mono (fun z hz => e.mem_source.mpr
      (((e.restrOpen A hA).mem_source.mp hz).1))
  · exact he.2.mono (fun z hz => e.mem_target.mpr
      (((e.restrOpen A hA).mem_target.mp hz).1))

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
