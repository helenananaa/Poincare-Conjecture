import PoincareConjecture.Topology.FiberSaturation.SmoothEmbeddingBoundary

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Manifold
open scoped Manifold ContDiff

variable {E F H G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [J.Boundaryless]

/-- The regular-domain boundary correspondence with standard smooth embedding
hypotheses. No HasAmbientModelCharts input and no reference-source placeholder. -/
theorem closedDomain_boundary_image {K : Set N}
    [ChartedSpace H K] [IsManifold I ∞ K]
    (hf : IsSmoothEmbedding I J ∞ (Subtype.val : K → N))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hK : IsClosed K) :
    (Subtype.val : K → N) '' I.boundary K = frontier K := by
  simpa only [Subtype.range_val] using smoothEmbedding_boundary_image hf hdim
    (by simpa only [Subtype.range_val] using hK)

/-- The blueprint's intrinsic boundary equality now implies regular openness
from the smooth closure inclusion itself, without assumed chart extensions. -/
theorem regularOpen_of_smoothClosure_boundary {D : Set N}
    [ChartedSpace H (closure D)] [IsManifold I ∞ (closure D)]
    (hD : IsOpen D)
    (hf : IsSmoothEmbedding I J ∞ (Subtype.val : closure D → N))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hb : (Subtype.val : closure D → N) '' I.boundary (closure D) = frontier D) :
    D = interior (closure D) := by
  apply regularOpen_of_frontier_closure_eq hD
  exact (closedDomain_boundary_image hf hdim isClosed_closure).symm.trans hb

/-- The complete boundary equality / regular-open equivalence for smooth
closures; the coordinate-compatibility assumption of the previous bridge is gone. -/
theorem smoothClosure_boundary_iff_regularOpen {D : Set N}
    [ChartedSpace H (closure D)] [IsManifold I ∞ (closure D)]
    (hD : IsOpen D)
    (hf : IsSmoothEmbedding I J ∞ (Subtype.val : closure D → N))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ((Subtype.val : closure D → N) '' I.boundary (closure D) = frontier D) ↔
      D = interior (closure D) := by
  constructor
  · exact regularOpen_of_smoothClosure_boundary hD hf hdim
  · intro hr
    exact (closedDomain_boundary_image hf hdim isClosed_closure).trans
      (MappingTorus.frontier_closure_eq_of_regularOpen hD hr)

/-- Closed-cylinder classification in genuine quotient coordinates, using the
original smooth-closure boundary input rather than an added regular-open premise.
The quotient-coordinate homeomorphism is still explicit; no smooth classification
or construction of a sphere bundle is claimed by this theorem. -/
theorem sphere_region_of_smoothClosure (φ : Sphere2 ≃ₜ Sphere2)
    {L : ℝ} (hL : 0 < L) (e : N ≃ₜ MappingTorus.Space φ.symm L)
    {D : Set N} [ChartedSpace H (closure D)] [IsManifold I ∞ (closure D)]
    (hD : IsOpen D) (hc : IsConnected D)
    (hf : IsSmoothEmbedding I J ∞ (Subtype.val : closure D → N))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hb : (Subtype.val : closure D → N) '' I.boundary (closure D) = frontier D)
    (hs : FiberSaturated (MappingTorus.proj φ.symm L ⁻¹' (e '' frontier D)))
    (hne : (frontier D).Nonempty) :
    Nonempty (↥(closure D) ≃ₜ (Sphere2 × Icc (0 : ℝ) 1)) := by
  have hr := regularOpen_of_smoothClosure_boundary hD hf hdim hb
  have hfront : FiberSaturated
      (MappingTorus.proj φ.symm L ⁻¹' frontier (e '' D)) := by
    rwa [e.image_frontier] at hs
  have hnonempty : (frontier (closure (e '' D))).Nonempty := by
    rw [← e.image_closure, ← e.image_frontier,
      MappingTorus.frontier_closure_eq_of_regularOpen hD hr]
    exact hne.image e
  obtain ⟨k⟩ := MappingTorus.region_closure_homeomorph φ.symm hL
    (e.isOpenMap _ hD) (hc.image _ e.continuous.continuousOn) hfront hnonempty
  exact ⟨(e.image (closure D)).trans
    ((Homeomorph.setCongr (e.image_closure D)).trans k)⟩

end PoincareConjecture.Topology.FiberSaturation
