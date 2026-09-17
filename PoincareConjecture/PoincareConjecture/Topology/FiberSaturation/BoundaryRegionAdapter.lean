import PoincareConjecture.Topology.FiberSaturation.BoundaryRegularity
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

section
variable {E H Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace Z]
  {I : ModelWithCorners ℝ E H} {D : Set Z} [ChartedSpace H (closure D)]

/-- Derive the previously explicit regular-open condition from actual
intrinsic boundary equality and locally compatible ambient charts. -/
theorem regularOpen_of_intrinsicBoundary_eq (hD : IsOpen D)
    (hcharts : HasAmbientModelCharts I (closure D))
    (hboundary : (Subtype.val : closure D → Z) '' I.boundary (closure D) = frontier D) :
    D = interior (closure D) := by
  apply regularOpen_of_frontier_closure_eq hD
  rw [← intrinsicBoundary_image_eq hcharts isClosed_closure]
  exact hboundary

/-- Under the verified chart condition, the blueprint boundary condition
and regular-openness are equivalent, not silently interchanged. -/
theorem intrinsicBoundary_eq_frontier_iff_regularOpen (hD : IsOpen D)
    (hcharts : HasAmbientModelCharts I (closure D)) :
    (Subtype.val : closure D → Z) '' I.boundary (closure D) = frontier D ↔
      D = interior (closure D) := by
  constructor
  · exact regularOpen_of_intrinsicBoundary_eq hD hcharts
  · intro hreg
    rw [intrinsicBoundary_image_eq hcharts isClosed_closure]
    exact MappingTorus.frontier_closure_eq_of_regularOpen hD hreg

end

/-- Source-facing sphere-quotient adapter. The original boundary equation
is used literally with Mathlib's manifold boundary. The required ambient
chart-extension witnesses remain explicit; their production from a general
smooth codimension-zero embedding is not claimed. -/
theorem sphere_quotient_region_of_boundaryCharts
    (φ : Sphere2 ≃ₜ Sphere2) {L : ℝ} (hL : 0 < L)
    {D : Set (MappingTorus.Space φ.symm L)}
    [ChartedSpace (EuclideanHalfSpace 3) (closure D)]
    (hD : IsOpen D) (hc : IsConnected D)
    (hcharts : HasAmbientModelCharts (modelWithCornersEuclideanHalfSpace 3) (closure D))
    (hboundary : (Subtype.val : closure D → MappingTorus.Space φ.symm L) ''
      (modelWithCornersEuclideanHalfSpace 3).boundary (closure D) = frontier D)
    (hfront : FiberSaturated (MappingTorus.proj φ.symm L ⁻¹' frontier D))
    (hne : (frontier D).Nonempty) :
    Nonempty (↥(closure D) ≃ₜ (Sphere2 × Icc (0 : ℝ) 1)) := by
  exact MappingTorus.sphere_bundle_quotient_regular_region φ hL hD hc
    (regularOpen_of_intrinsicBoundary_eq hD hcharts hboundary) hfront hne

end PoincareConjecture.Topology.FiberSaturation
