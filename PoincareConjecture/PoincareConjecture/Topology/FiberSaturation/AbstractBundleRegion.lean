import PoincareConjecture.Topology.FiberSaturation.AbstractRealPresentation
import PoincareConjecture.Topology.FiberSaturation.PresentedSmoothRegion

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Function Bundle Manifold
open scoped Manifold ContDiff

/-- Membership in S is constant on each actual fiber of a projection. -/
def ProjectionSaturated {Z B : Type*} (prj : Z → B) (S : Set Z) : Prop :=
  ∀ ⦃z w⦄, prj z = prj w → z ∈ S → w ∈ S

/-- Saturation of an intrinsic bundle boundary pulls back to product fibers
for any map that preserves the base coordinate. -/
theorem projectionSaturated_pullback {X Y Z B : Type*}
    (prj : Z → B) (q : X × Y → Z) (c : Y → B) {S : Set Z}
    (hs : ProjectionSaturated prj S) (hb : ∀ p, prj (q p) = c p.2) :
    FiberSaturated (q ⁻¹' S) := by
  intro x y t hx
  exact hs ((hb (x,t)).trans (hb (y,t)).symm) hx

/-- Topological regular-region classification in a genuine abstract sphere
bundle. No monodromy, global coordinates, cut trivialization or q is an input. -/
theorem abstract_sphere_bundle_regular_region
    {L : ℝ} (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
    [TopologicalSpace (TotalSpace Sphere2 E)] [FiberBundle Sphere2 E]
    [T2Space (TotalSpace Sphere2 E)] (hL : 0 < L)
    {D : Set (TotalSpace Sphere2 E)} (hD : IsOpen D) (hc : IsConnected D)
    (hr : D = interior (closure D))
    (hs : ProjectionSaturated (Bundle.TotalSpace.proj (F := Sphere2) (E := E)) (frontier D))
    (hne : (frontier D).Nonempty) :
    Nonempty (↥(closure D) ≃ₜ (Sphere2 × Icc (0 : ℝ) 1)) := by
  obtain ⟨φ,q,hq,hqs,hbase,hfiber,hglue,_⟩ :=
    CircleBundle.abstract_sphere_bundle_real_presentation E hL
  have hsat := projectionSaturated_pullback _ q (fun t : ℝ => (t : AddCircle L)) hs hbase
  obtain ⟨e,he⟩ := sphere_presentation_coordinates φ hL q _ hq
    (FiberBundle.continuous_proj Sphere2 E) hqs hbase hfiber hglue
  have hinv (p : Sphere2 × ℝ) : e.symm (MappingTorus.proj φ.symm L p) = q p := by
    rw [← he p,e.symm_apply_apply]
  have hpull : MappingTorus.proj φ.symm L ⁻¹' (e '' frontier D) = q ⁻¹' frontier D := by
    simpa only [Homeomorph.symm_symm] using
      MappingTorus.presentation_preimage_inverse_image φ.symm L q e.symm hinv (frontier D)
  have hfront : FiberSaturated (MappingTorus.proj φ.symm L ⁻¹' frontier (e '' D)) := by
    rw [← e.image_frontier,hpull]
    exact hsat
  have hn : (frontier (closure (e '' D))).Nonempty := by
    rw [← e.image_closure,← e.image_frontier,
      MappingTorus.frontier_closure_eq_of_regularOpen hD hr]
    exact hne.image e
  obtain ⟨k⟩ := MappingTorus.region_closure_homeomorph φ.symm hL
    (e.isOpenMap _ hD) (hc.image _ e.continuous.continuousOn) hfront hn
  exact ⟨(e.image (closure D)).trans ((Homeomorph.setCongr (e.image_closure D)).trans k)⟩

section SmoothClosure
variable {L : ℝ} (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
  [TopologicalSpace (TotalSpace Sphere2 E)] [FiberBundle Sphere2 E]
  [T2Space (TotalSpace Sphere2 E)]
  {V W H G : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace H] [TopologicalSpace G] [ChartedSpace G (TotalSpace Sphere2 E)]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G} [J.Boundaryless]

/-- Intrinsic smooth-closure boundary data in the original abstract bundle
now suffice for the topological classification without any chosen presentation.
This does not assert that the constructed topological presentation is smooth. -/
theorem abstract_sphere_bundle_smoothClosure_region (hL : 0 < L)
    {D : Set (TotalSpace Sphere2 E)}
    [ChartedSpace H (closure D)] [IsManifold I ∞ (closure D)]
    (hD : IsOpen D) (hc : IsConnected D)
    (hf : IsSmoothEmbedding I J ∞ (Subtype.val : closure D → TotalSpace Sphere2 E))
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (hb : (Subtype.val : closure D → TotalSpace Sphere2 E) '' I.boundary (closure D) = frontier D)
    (hs : ProjectionSaturated (Bundle.TotalSpace.proj (F := Sphere2) (E := E)) (frontier D))
    (hne : (frontier D).Nonempty) :
    Nonempty (↥(closure D) ≃ₜ (Sphere2 × Icc (0 : ℝ) 1)) := by
  exact abstract_sphere_bundle_regular_region E hL hD hc
    (regularOpen_of_smoothClosure_boundary hD hf hdim hb) hs hne

end SmoothClosure
end PoincareConjecture.Topology.FiberSaturation
