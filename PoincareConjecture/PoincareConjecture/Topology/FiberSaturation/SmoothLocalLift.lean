import PoincareConjecture.Topology.FiberSaturation.CoverLiftLocalDiffeomorph

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Manifold Filter
open scoped Manifold ContDiff Topology
variable {V W E H G K A M N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace K]
  [TopologicalSpace A] [ChartedSpace K A]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G}
  {Q : ModelWithCorners ℝ E K}

/-- A continuous lift through a local diffeomorphism is smooth whenever its
projection is smooth. Smoothness of the lift is proved, not assumed. -/
theorem contMDiff_of_localDiffeomorph_comp {f : A → M} {g : M → N}
    (hg : IsLocalDiffeomorph I J ∞ g) (hf : Continuous f)
    (hcomp : ContMDiff Q J ∞ (g ∘ f)) : ContMDiff Q I ∞ f := by
  intro x
  let h := hg (f x)
  have hn : ∀ᶠ y in nhds x, f y ∈ h.localInverse.target :=
    hf.continuousAt (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)
  have heq : (h.localInverse ∘ (g ∘ f)) =ᶠ[nhds x] f := by
    filter_upwards [hn] with y hy
    exact h.localInverse_left_inv hy
  exact (h.localInverse_contMDiffAt.comp x (hcomp x)).congr_of_eventuallyEq heq.symm

/-- Every deck homeomorphism of a smooth local diffeomorphism is already a
smooth diffeomorphism for the specified source and target structures. -/
def deckDiffeomorph {g : M → N} (hg : IsLocalDiffeomorph I J ∞ g)
    (T : M ≃ₜ M) (hT : ∀ x, g (T x) = g x) : M ≃ₘ⟮I,I⟯ M where
  toEquiv := T.toEquiv
  contMDiff_toFun := contMDiff_of_localDiffeomorph_comp hg T.continuous
    (hg.contMDiff.congr hT)
  contMDiff_invFun := contMDiff_of_localDiffeomorph_comp hg T.symm.continuous
    (hg.contMDiff.congr (fun x => by
      change g (T.symm x) = g x
      simpa only [T.apply_symm_apply] using (hT (T.symm x)).symm))

end PoincareConjecture.Topology.FiberSaturation
