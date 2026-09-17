import PoincareConjecture.Topology.FiberSaturation.TorusRegionClassification
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- The topological bridge needed when the source identifies the boundary of
the closure with the frontier of an open region. No regularity is assumed. -/
theorem regularOpen_of_frontier_closure_eq {Z : Type*} [TopologicalSpace Z]
    {D : Set Z} (hD : IsOpen D) (hfront : frontier (closure D) = frontier D) :
    D = interior (closure D) := by
  apply Subset.antisymm
  · exact hD.subset_interior_iff.mpr subset_closure
  · intro x hx
    by_contra hn
    have hf : x ∈ frontier D := by
      rw [hD.frontier_eq]
      exact ⟨interior_subset hx, hn⟩
    rw [← hfront] at hf
    exact hf.2 hx

section ModelCharts
variable {E H Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace Z]
  (I : ModelWithCorners ℝ E H) (K : Set Z) [ChartedSpace H K]

/-- Explicit ambient chart extensions of the intrinsic chart at each point.
The input is a local set model and pointwise chart compatibility, not a
boundary-equality or regular-open assumption. Existence from a general smooth
embedding is a separate theorem and is NOT asserted here. -/
def HasAmbientModelCharts : Prop :=
  ∀ p : K, ∃ e : OpenPartialHomeomorph Z E,
    p.1 ∈ e.source ∧ e.IsImage K (range I) ∧ e p.1 = extChartAt I p p

variable {I K}

/-- Local straightening identifies the actual intrinsic interior. -/
theorem intrinsicInterior_iff_ambientInterior (h : HasAmbientModelCharts I K)
    (p : K) : I.IsInteriorPoint p ↔ p.1 ∈ interior K := by
  obtain ⟨e, hp, he, hcoord⟩ := h p
  change extChartAt I p p ∈ interior (range I) ↔ p.1 ∈ interior K
  rw [← hcoord]
  exact he.interior hp

/-- Local straightening identifies the actual intrinsic boundary. -/
theorem intrinsicBoundary_iff_ambientFrontier (h : HasAmbientModelCharts I K)
    (p : K) : I.IsBoundaryPoint p ↔ p.1 ∈ frontier K := by
  obtain ⟨e, hp, he, hcoord⟩ := h p
  change extChartAt I p p ∈ frontier (range I) ↔ p.1 ∈ frontier K
  rw [← hcoord]
  exact he.frontier hp

/-- The subtype inclusion sends intrinsic interior exactly to ambient interior. -/
theorem intrinsicInterior_image_eq (h : HasAmbientModelCharts I K) :
    (Subtype.val : K → Z) '' I.interior K = interior K := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (intrinsicInterior_iff_ambientInterior h p).mp hp
  · intro hx
    exact ⟨⟨x, interior_subset hx⟩,
      (intrinsicInterior_iff_ambientInterior h _).mpr hx, rfl⟩

/-- Closedness ensures every ambient frontier point belongs to the domain. -/
theorem intrinsicBoundary_image_eq (h : HasAmbientModelCharts I K)
    (hK : IsClosed K) : (Subtype.val : K → Z) '' I.boundary K = frontier K := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (intrinsicBoundary_iff_ambientFrontier h p).mp hp
  · intro hx
    have hxK : x ∈ K := hK.closure_eq ▸ hx.1
    exact ⟨⟨x, hxK⟩, (intrinsicBoundary_iff_ambientFrontier h _).mpr hx, rfl⟩

end ModelCharts
end PoincareConjecture.Topology.FiberSaturation
