import PoincareConjecture.Topology.FiberSaturation.SmoothCylinder
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Manifold Filter
open scoped Manifold ContDiff Topology

variable {E F V T H G W B M P A N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace W] [TopologicalSpace B]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace G P]
  [TopologicalSpace A] [ChartedSpace W A]
  [TopologicalSpace N] [ChartedSpace B N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {K : ModelWithCorners ℝ V W} {L : ModelWithCorners ℝ T B}
  {f : M → A} {g : P → N} {q : A → N}

/-- The inverse comparison is smooth by using local smooth inverses of q.
No global inverse of q and no change of manifold structures are required. -/
theorem comparison_inverse_contMDiff (hf : IsSmoothEmbedding I K ∞ f)
    (hg : IsSmoothEmbedding J L ∞ g) (hq : IsLocalDiffeomorph K L ∞ q)
    (e : M ≃ₜ P) (he : ∀ x, g (e x) = q (f x)) : ContMDiff J I ∞ e.symm := by
  apply (ContMDiff.iff_comp_isImmersion hf.isImmersion).mpr
  refine ⟨e.symm.continuous, ?_⟩
  have hpoint (y : P) : g y = q (f (e.symm y)) := by
    simpa only [e.apply_symm_apply] using he (e.symm y)
  intro y
  let h := hq (f (e.symm y))
  have hd : ContMDiffAt L K ∞ h.localInverse (g y) := by
    rw [hpoint]; exact h.localInverse_contMDiffAt
  have hnear : ∀ᶠ z in nhds y, f (e.symm z) ∈ h.localInverse.target :=
    (hf.contMDiff.continuous.comp e.symm.continuous).continuousAt
      (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)
  have heq : (h.localInverse ∘ g) =ᶠ[nhds y] (f ∘ e.symm) := by
    filter_upwards [hnear] with z hz
    change h.localInverse (g z) = f (e.symm z)
    rw [hpoint]
    exact h.localInverse_left_inv hz
  exact (hd.comp y hg.contMDiff.contMDiffAt).congr_of_eventuallyEq heq.symm

/-- Upgrade a checked topological comparison through a local diffeomorphism.
The inverse smoothness follows from the previous theorem, not a new input. -/
def diffeomorphOfLocalDiffeomorphComparison (hf : IsSmoothEmbedding I K ∞ f)
    (hg : IsSmoothEmbedding J L ∞ g) (hq : IsLocalDiffeomorph K L ∞ q)
    (e : M ≃ₜ P) (he : ∀ x, g (e x) = q (f x)) : M ≃ₘ⟮I, J⟯ P where
  toEquiv := e.toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.iff_comp_isImmersion hg.isImmersion).mpr
    refine ⟨e.continuous, ?_⟩
    have hcomp : g ∘ e = q ∘ f := funext he
    exact hcomp.symm ▸ (hq.contMDiff.comp hf.contMDiff)
  contMDiff_invFun := comparison_inverse_contMDiff hf hg hq e he

@[simp] theorem diffeomorphOfLocalDiffeomorphComparison_apply
    (hf : IsSmoothEmbedding I K ∞ f) (hg : IsSmoothEmbedding J L ∞ g)
    (hq : IsLocalDiffeomorph K L ∞ q) (e : M ≃ₜ P)
    (he : ∀ x, g (e x) = q (f x)) (x : M) :
    diffeomorphOfLocalDiffeomorphComparison hf hg hq e he x = e x := rfl

end PoincareConjecture.Topology.FiberSaturation
