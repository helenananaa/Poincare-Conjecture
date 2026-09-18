import PoincareConjecture.Topology.FiberSaturation.CoverLiftAtlas

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

/-- The source atlas is smooth because each transition is an actual restriction
of a smooth transition from the unchanged target manifold. -/
theorem isManifold : letI := chartedSpace (H := H) hf; IsManifold I ∞ M := by
  letI := chartedSpace (H := H) hf
  apply isManifold_of_contDiffOn I ∞ M
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  have h := (contDiffGroupoid ∞ I).compatible
    (chart_mem_atlas H (f x)) (chart_mem_atlas H (f y))
  refine (h.1.mono ?_).congr ?_
  · intro u hu
    exact ⟨transition_source_subset hf x y hu.1, hu.2⟩
  · intro u hu
    exact congrArg I (transition_eq hf x y hu.1)

end PoincareConjecture.Topology.FiberSaturation.CoverLift
