import PoincareConjecture.Topology.FiberSaturation.AbstractSmoothPresentation
import PoincareConjecture.Topology.FiberSaturation.AbstractBoundaryPairing
import PoincareConjecture.Topology.FiberSaturation.SmoothPresentedCylinder

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Function Bundle Manifold
open scoped Manifold ContDiff
variable {L : ℝ} (E : AddCircle L → Type*) [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace Sphere2 E)] [FiberBundle Sphere2 E]
  [T2Space (TotalSpace Sphere2 E)]
  {V W H G : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace H] [TopologicalSpace G] [ChartedSpace G (TotalSpace Sphere2 E)]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G} [J.Boundaryless]
  [IsManifold J ∞ (TotalSpace Sphere2 E)]

local instance : ChartedSpace ℝ (AddCircle L) := CircleSmooth.chartedSpace L

/-- Smooth cylinder classification directly from an actual locally smooth
sphere-bundle atlas and intrinsic closure-boundary data. No presentation,
deck map, pullback smoothness or regular-open assumption is supplied. -/
theorem abstract_smooth_sphere_bundle_region (hL : 0 < L)
    (hloc : ∀ b : AddCircle L, ∃ k : Trivialization Sphere2
        (TotalSpace.proj (F := Sphere2) (E := E)),
      b ∈ k.baseSet ∧ SmoothBundle.IsSmoothBundleChart 𝓘(ℝ,ℝ) J (𝓡 2) k)
    {D : Set (TotalSpace Sphere2 E)}
    [ChartedSpace H (closure D)] [IsManifold I ∞ (closure D)]
    (hD : IsOpen D) (hc : IsConnected D)
    (hf : IsSmoothEmbedding I J ∞ (Subtype.val : closure D → TotalSpace Sphere2 E))
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (hb : (Subtype.val : closure D → TotalSpace Sphere2 E) '' I.boundary (closure D) = frontier D)
    (hs : ProjectionSaturated (TotalSpace.proj (F := Sphere2) (E := E)) (frontier D))
    (hne : (frontier D).Nonempty) :
    Nonempty (↥(closure D) ≃ₘ⟮I,(𝓡 2).prod (𝓡∂ 1)⟯ (Sphere2 × Icc (0 : ℝ) 1)) := by
  obtain ⟨φ,q,hq,hqs,hbase,hfiber,hglue⟩ :=
    SmoothBundle.abstract_bundle_smooth_real_presentation E hL hloc
  have hsat := projectionSaturated_pullback _ q
    ((↑) : ℝ → AddCircle L) hs hbase
  exact sphere_region_diffeomorph_of_smoothPresentation φ.toHomeomorph hL q
    TotalSpace.proj hq (FiberBundle.continuous_proj Sphere2 E) hqs
    hbase hfiber hglue hD hc hf hdim hb hsat hne

/-- Smooth closed-cylinder classification together with the two genuine
connected components of the original bundle boundary. -/
theorem abstract_smooth_sphere_bundle_boundary_pairing (hL : 0 < L)
    (hloc : ∀ b : AddCircle L, ∃ k : Trivialization Sphere2
        (TotalSpace.proj (F := Sphere2) (E := E)),
      b ∈ k.baseSet ∧ SmoothBundle.IsSmoothBundleChart 𝓘(ℝ,ℝ) J (𝓡 2) k)
    {D : Set (TotalSpace Sphere2 E)}
    [ChartedSpace H (closure D)] [IsManifold I ∞ (closure D)]
    (hD : IsOpen D) (hc : IsConnected D)
    (hf : IsSmoothEmbedding I J ∞ (Subtype.val : closure D → TotalSpace Sphere2 E))
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (hb : (Subtype.val : closure D → TotalSpace Sphere2 E) '' I.boundary (closure D) = frontier D)
    (hs : ProjectionSaturated (TotalSpace.proj (F := Sphere2) (E := E)) (frontier D))
    (hne : (frontier D).Nonempty) :
    Nonempty (↥(closure D) ≃ₘ⟮I,(𝓡 2).prod (𝓡∂ 1)⟯ (Sphere2 × Icc (0 : ℝ) 1)) ∧
    ∃ u v : AddCircle L, u ≠ v ∧
      let A := (TotalSpace.proj (F := Sphere2) (E := E)) ⁻¹' {u}
      let B := (TotalSpace.proj (F := Sphere2) (E := E)) ⁻¹' {v}
      frontier D = A ∪ B ∧ IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
        (∀ z ∈ A, connectedComponentIn (frontier D) z = A) ∧
        (∀ z ∈ B, connectedComponentIn (frontier D) z = B) := by
  exact ⟨abstract_smooth_sphere_bundle_region E hL hloc hD hc hf hdim hb hs hne,
    abstract_sphere_bundle_boundary_components E hL hD hc
      (regularOpen_of_smoothClosure_boundary hD hf hdim hb) hs hne⟩

end PoincareConjecture.Topology.FiberSaturation
