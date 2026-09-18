import PoincareConjecture.Topology.FiberSaturation.CoverLiftSmooth

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CoverLift
open Set Manifold
open scoped Manifold ContDiff Topology
variable {V H M N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H N] {f : M → N}
  (I : ModelWithCorners ℝ V H) [IsManifold I ∞ N]
  (hf : IsLocalHomeomorph f)

/-- The original map becomes a local diffeomorphism for the lifted source
atlas, with the original smooth structure on the target left unchanged. -/
theorem isLocalDiffeomorph :
    letI := chartedSpace (H := H) hf; IsLocalDiffeomorph I I ∞ f := by
  letI := chartedSpace (H := H) hf
  letI : IsManifold I ∞ M := isManifold I hf
  intro x
  let a : PartialDiffeomorph I I M H ∞ :=
    { toPartialEquiv := (chart (H := H) hf x).toPartialEquiv
      open_source := (chart (H := H) hf x).open_source
      open_target := (chart (H := H) hf x).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  let b : PartialDiffeomorph I I N H ∞ :=
    { toPartialEquiv := (chartAt H (f x)).toPartialEquiv
      open_source := (chartAt H (f x)).open_source
      open_target := (chartAt H (f x)).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  refine ⟨a.trans b.symm, ?_, ?_⟩
  · refine ⟨mem_chart_source H x, ?_⟩
    change chart (H := H) hf x x ∈ (chartAt H (f x)).target
    rw [chart_apply]
    exact mem_chart_target H (f x)
  · intro z hz
    change f z = (chartAt H (f x)).symm (chart (H := H) hf x z)
    rw [chart_apply]
    have hsource := hz.1.2
    change (hf.localInverseAt x).symm z ∈ (chartAt H (f x)).source at hsource
    rw [hf.localInverseAt_symm] at hsource
    exact ((chartAt H (f x)).left_inv hsource).symm

end PoincareConjecture.Topology.FiberSaturation.CoverLift
