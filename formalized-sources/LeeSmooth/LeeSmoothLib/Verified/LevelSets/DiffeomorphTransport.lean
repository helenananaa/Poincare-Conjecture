import Mathlib
import LeeSmoothLib.Ch04.Sec04_21.Exercise_4_4
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3

open scoped Manifold ContDiff
open Manifold Function
noncomputable section
namespace LeeVerifiedLevelSets.DiffeomorphTransport

private lemma finrank_range_conjugate
    {E₀ E₁ E₂ E₃ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    (A : E₀ →L[ℝ] E₁) (l : E₁ ≃L[ℝ] E₂) (r : E₃ ≃L[ℝ] E₀) :
    Module.finrank ℝ ((l.toContinuousLinearMap.comp A).comp r.toContinuousLinearMap).range =
      Module.finrank ℝ A.range := by
  change Module.finrank ℝ
    ((l.toLinearEquiv.toLinearMap.comp A.toLinearMap).comp r.toLinearEquiv.toLinearMap).range = _
  rw [LinearMap.range_comp_of_range_eq_top _ r.toLinearEquiv.range,
    LinearMap.range_comp, LinearEquiv.finrank_map_eq]

variable {E E' E₁ E₂ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable {H H' H₁ H₂ : Type*}
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace H₁] [TopologicalSpace H₂]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {I₁ : ModelWithCorners ℝ E₁ H₁} {J₁ : ModelWithCorners ℝ E₂ H₂}
variable {M N M₁ N₁ : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace N₁] [ChartedSpace H₂ N₁]
variable (a : M₁ ≃ₘ⟮I₁, I⟯ M) (b : N ≃ₘ⟮J, J₁⟯ N₁)
  {f : M → N} (hf : ContMDiff I J ∞ f)

include hf

/-- Coordinate changes conjugate the derivative by genuine linear equivalences. -/
theorem mfderiv_comp_diffeomorphs (x : M₁) :
    mfderiv I₁ J₁ (b ∘ f ∘ a) x =
      ((b.mfderivToContinuousLinearEquiv (by simp) (f (a x))).toContinuousLinearMap.comp
        (mfderiv I J f (a x))).comp
          (a.mfderivToContinuousLinearEquiv (by simp) x).toContinuousLinearMap := by
  rw [mfderiv_comp x (b.contMDiff.mdifferentiableAt (by simp)) ((hf.comp a.contMDiff).mdifferentiableAt (by simp))]
  rw [mfderiv_comp x (hf.mdifferentiableAt (by simp)) (a.contMDiff.mdifferentiableAt (by simp))]
  simp only [Diffeomorph.mfderivToContinuousLinearEquiv_coe, ContinuousLinearMap.comp_assoc]
  rfl

/-- Surjectivity of the differential is invariant under changes of manifold coordinates. -/
theorem surjective_mfderiv_comp_diffeomorphs_iff (x : M₁) :
    Surjective (mfderiv I₁ J₁ (b ∘ f ∘ a) x) ↔
      Surjective (mfderiv I J f (a x)) := by
  rw [mfderiv_comp_diffeomorphs a b hf x]
  let l := b.mfderivToContinuousLinearEquiv (by simp) (f (a x))
  let r := a.mfderivToContinuousLinearEquiv (by simp) x
  let A := mfderiv I J f (a x)
  change Surjective (fun v => l (A (r v))) ↔ Surjective A
  constructor
  · intro h z
    obtain ⟨v, hv⟩ := h (l z)
    exact ⟨r v, l.injective hv⟩
  · intro h
    exact l.surjective.comp (h.comp r.surjective)

/-- Rank is invariant under independent diffeomorphisms of domain and target. -/
theorem rankAt_comp_diffeomorphs (x : M₁) :
    rankAt I₁ J₁ (b ∘ f ∘ a) x = rankAt I J f (a x) := by
  unfold rankAt
  rw [mfderiv_comp_diffeomorphs a b hf x]
  unfold TangentSpace
  exact finrank_range_conjugate _ _ _

/-- Regular values transport without an additional boundary or dimension assumption. -/
theorem isRegularValue_comp_diffeomorphs_iff (c : N) :
    IsRegularValue I₁ J₁ (b ∘ f ∘ a) (b c) ↔ IsRegularValue I J f c := by
  constructor
  · intro h p hp
    have hasurj : Surjective (a : M₁ → M) := a.surjective
    obtain ⟨x, rfl⟩ := hasurj p
    exact (surjective_mfderiv_comp_diffeomorphs_iff a b hf x).mp
      (h x (congrArg b hp))
  · intro h x hx
    apply (surjective_mfderiv_comp_diffeomorphs_iff a b hf x).mpr
    exact h (a x) (b.injective hx)

/-- Constant-rank hypotheses can be transported through a charted-space replacement. -/
theorem hasConstantRank_comp_diffeomorphs_iff (r : ℕ) :
    HasConstantRank I₁ J₁ (b ∘ f ∘ a) r ↔ HasConstantRank I J f r := by
  constructor
  · intro h
    refine ⟨hf.mdifferentiable (by simp), ?_⟩
    intro p
    have hasurj : Surjective (a : M₁ → M) := a.surjective
    obtain ⟨x, rfl⟩ := hasurj p
    rw [← rankAt_comp_diffeomorphs a b hf x]
    exact h.2 x
  · intro h
    refine ⟨(b.contMDiff.comp (hf.comp a.contMDiff)).mdifferentiable (by simp), ?_⟩
    intro x
    rw [rankAt_comp_diffeomorphs a b hf x]
    exact h.2 (a x)

end LeeVerifiedLevelSets.DiffeomorphTransport
end
