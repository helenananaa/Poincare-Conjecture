import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CoverLift
open Set Manifold
open scoped Manifold ContDiff Topology
variable {V H M N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H N] {f : M → N}

/-- Lift an existing target chart through a genuine local inverse sheet. -/
def chart (hf : IsLocalHomeomorph f) (x : M) : OpenPartialHomeomorph M H :=
  (hf.localInverseAt x).symm.trans (chartAt H (f x))

@[simp] theorem chart_apply (hf : IsLocalHomeomorph f) (x z : M) :
    chart (H := H) hf x z = chartAt H (f x) (f z) := by
  change chartAt H (f x) ((hf.localInverseAt x).symm z) = _
  rw [hf.localInverseAt_symm]

/-- Only the new source receives an atlas; the target's atlas is unchanged. -/
@[implicit_reducible] def chartedSpace (hf : IsLocalHomeomorph f) : ChartedSpace H M where
  atlas := range (chart (H := H) hf)
  chartAt := chart (H := H) hf
  mem_chart_source x := by simp [chart]
  chart_mem_atlas x := mem_range_self x

/-- The inverse chart projects to the original target inverse chart. -/
theorem project_chart_symm (hf : IsLocalHomeomorph f) (x : M) {u : H}
    (hu : u ∈ (chart (H := H) hf x).target) :
    f ((chart (H := H) hf x).symm u) = (chartAt H (f x)).symm u := by
  exact hf.apply_localInverseAt_of_mem hu.2

/-- All lifted transitions are restrictions of the original transitions. -/
theorem transition_source_subset (hf : IsLocalHomeomorph f) (x y : M) :
    ((chart (H := H) hf x).symm.trans (chart (H := H) hf y)).source ⊆
      ((chartAt H (f x)).symm.trans (chartAt H (f y))).source := by
  intro u hu
  refine ⟨hu.1.1, ?_⟩
  have hh : f ((chart (H := H) hf x).symm u) ∈ (chartAt H (f y)).source := by
    have hh := hu.2.2
    change (hf.localInverseAt y).symm ((chart (H := H) hf x).symm u) ∈
      (chartAt H (f y)).source at hh
    rwa [hf.localInverseAt_symm] at hh
  rwa [project_chart_symm hf x hu.1] at hh

theorem transition_eq (hf : IsLocalHomeomorph f) (x y : M) {u : H}
    (hu : u ∈ ((chart (H := H) hf x).symm.trans (chart (H := H) hf y)).source) :
    (chart (H := H) hf y) ((chart (H := H) hf x).symm u) =
      (chartAt H (f y)) ((chartAt H (f x)).symm u) := by
  rw [chart_apply, project_chart_symm hf x hu.1]

end PoincareConjecture.Topology.FiberSaturation.CoverLift
