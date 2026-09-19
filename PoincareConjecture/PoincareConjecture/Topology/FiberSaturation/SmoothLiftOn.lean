import PoincareConjecture.Topology.FiberSaturation.NativeCirclePullback

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

/-- The smooth-lifting principle at one point; continuity excludes jumps
between different sheets of the local diffeomorphism. -/
theorem contMDiffAt_of_localDiffeomorph_comp {f : A → M} {g : M → N} {x : A}
    (hg : IsLocalDiffeomorphAt I J ∞ g (f x)) (hf : ContinuousAt f x)
    (hcomp : ContMDiffAt Q J ∞ (g ∘ f) x) : ContMDiffAt Q I ∞ f x := by
  have hn : ∀ᶠ y in nhds x, f y ∈ hg.localInverse.target :=
    hf (hg.localInverse.open_target.mem_nhds hg.localInverse_mem_target)
  have heq : (hg.localInverse ∘ (g ∘ f)) =ᶠ[nhds x] f := by
    filter_upwards [hn] with y hy
    exact hg.localInverse_left_inv hy
  exact (hg.localInverse_contMDiffAt.comp x hcomp).congr_of_eventuallyEq heq.symm

/-- A chart-domain form of smooth lifting. Neither map is required to
have useful values outside the stated open domain. -/
theorem contMDiffOn_of_localDiffeomorph_comp {f : A → M} {g : M → N} {s : Set A}
    (hg : IsLocalDiffeomorph I J ∞ g) (hs : IsOpen s) (hf : ContinuousOn f s)
    (hcomp : ContMDiffOn Q J ∞ (g ∘ f) s) : ContMDiffOn Q I ∞ f s := by
  intro x hx
  exact (contMDiffAt_of_localDiffeomorph_comp (hg (f x))
    ((hf x hx).continuousAt (hs.mem_nhds hx))
    (hcomp.contMDiffAt (hs.mem_nhds hx))).contMDiffWithinAt

end PoincareConjecture.Topology.FiberSaturation
