import PoincareConjecture.Topology.FiberSaturation.TorusFrontierFibers
import PoincareConjecture.Topology.FiberSaturation.FrontierComponents

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Bundle Function

variable {L : ℝ} (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
  [TopologicalSpace (TotalSpace Sphere2 E)] [FiberBundle Sphere2 E]
  [T2Space (TotalSpace Sphere2 E)]

/-- The two boundary heights are points of the original bundle base, not
chosen labels on an unrelated cylinder. -/
theorem abstract_sphere_bundle_frontier_pair (hL : 0 < L)
    {D : Set (TotalSpace Sphere2 E)} (ho : IsOpen D) (hc : IsConnected D)
    (hr : D = interior (closure D))
    (hs : ProjectionSaturated (TotalSpace.proj (F := Sphere2) (E := E)) (frontier D))
    (hn : (frontier D).Nonempty) :
    ∃ u v : AddCircle L, u ≠ v ∧
      frontier D = TotalSpace.proj ⁻¹' ({u,v} : Set (AddCircle L)) := by
  obtain ⟨φ,q,hq,hqs,hbase,hfiber,hglue,_⟩ :=
    CircleBundle.abstract_sphere_bundle_real_presentation E hL
  obtain ⟨e,he⟩ := sphere_presentation_coordinates φ hL q _ hq
    (FiberBundle.continuous_proj Sphere2 E) hqs hbase hfiber hglue
  have hebase (z : TotalSpace Sphere2 E) :
      MappingTorus.circleProjection φ.symm L (e z) = z.proj := by
    obtain ⟨p,rfl⟩ := hqs z
    rw [he, MappingTorus.circleProjection_proj]
    exact (hbase p).symm
  have hsat : FiberSaturated (MappingTorus.proj φ.symm L ⁻¹' frontier (e '' D)) := by
    rw [← e.image_frontier]
    intro x y t hx
    have hx' : q (x,t) ∈ frontier D := by
      change MappingTorus.proj φ.symm L (x,t) ∈ e '' frontier D at hx
      rw [← he] at hx
      exact (e.injective.mem_set_image).mp hx
    have hy' : q (y,t) ∈ frontier D := hs ((hbase (x,t)).trans (hbase (y,t)).symm) hx'
    change MappingTorus.proj φ.symm L (y,t) ∈ e '' frontier D
    rw [← he]
    exact mem_image_of_mem e hy'
  have hn' : (frontier (closure (e '' D))).Nonempty := by
    rw [← e.image_closure, ← e.image_frontier,
      MappingTorus.frontier_closure_eq_of_regularOpen ho hr]
    exact hn.image e
  obtain ⟨u,v,huv,hfr⟩ := MappingTorus.region_frontier_circle_pair φ.symm hL
    (e.isOpenMap _ ho) (hc.image _ e.continuous.continuousOn) hsat hn'
  refine ⟨u,v,huv,?_⟩
  have hpull := congrArg (fun S => e ⁻¹' S) hfr
  rw [← e.image_frontier, preimage_image_eq _ e.injective] at hpull
  exact hpull.trans (by ext z; change _ ∈ ({u,v} : Set (AddCircle L)) ↔ _; rw [hebase]; rfl)

omit [T2Space (TotalSpace Sphere2 E)] in
/-- Each actual bundle fiber is connected and nonempty, by its supplied
local trivialization and the proved connectedness of the Euclidean sphere. -/
theorem abstract_sphere_bundle_fiber_connected (t : AddCircle L) :
    IsConnected ((TotalSpace.proj (F := Sphere2) (E := E)) ⁻¹' {t}) := by
  let e := (trivializationAt Sphere2 E t).preimageSingletonHomeomorph
    (mem_baseSet_trivializationAt Sphere2 E t)
  have h : IsConnected (univ : Set ((TotalSpace.proj (F := Sphere2) (E := E)) ⁻¹' {t})) := by
    simpa only [preimage_univ] using e.isConnected_preimage.mpr isConnected_univ
  simpa only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq] using
    h.image Subtype.val continuous_subtype_val.continuousOn

/-- The boundary has precisely two nonempty disjoint connected components;
both are whole fibers of the original sphere-bundle projection. -/
theorem abstract_sphere_bundle_boundary_components (hL : 0 < L)
    {D : Set (TotalSpace Sphere2 E)} (ho : IsOpen D) (hc : IsConnected D)
    (hr : D = interior (closure D))
    (hs : ProjectionSaturated (TotalSpace.proj (F := Sphere2) (E := E)) (frontier D))
    (hn : (frontier D).Nonempty) :
    ∃ u v : AddCircle L, u ≠ v ∧
      let A := (TotalSpace.proj (F := Sphere2) (E := E)) ⁻¹' {u}
      let B := (TotalSpace.proj (F := Sphere2) (E := E)) ⁻¹' {v}
      frontier D = A ∪ B ∧ IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
        (∀ z ∈ A, connectedComponentIn (frontier D) z = A) ∧
        (∀ z ∈ B, connectedComponentIn (frontier D) z = B) := by
  letI : Fact (0 < L) := ⟨hL⟩
  obtain ⟨u,v,huv,hpair⟩ := abstract_sphere_bundle_frontier_pair E hL ho hc hr hs hn
  let A := (TotalSpace.proj (F := Sphere2) (E := E)) ⁻¹' {u}
  let B := (TotalSpace.proj (F := Sphere2) (E := E)) ⁻¹' {v}
  have hfr : frontier D = A ∪ B := by
    rw [hpair]
    ext z
    simp [A,B]
  have hA : IsConnected A := abstract_sphere_bundle_fiber_connected E u
  have hB : IsConnected B := abstract_sphere_bundle_fiber_connected E v
  have hAc : IsClosed A := isClosed_singleton.preimage (FiberBundle.continuous_proj Sphere2 E)
  have hBc : IsClosed B := isClosed_singleton.preimage (FiberBundle.continuous_proj Sphere2 E)
  have hd : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hz hz'
    exact huv ((show z.proj = u from hz).symm.trans (show z.proj = v from hz'))
  refine ⟨u,v,huv,hfr,hA,hB,hd,?_,?_⟩
  · intro z hz
    rw [hfr]
    exact componentIn_disjoint_closed_union hAc hBc hA.2 hd hz
  · intro z hz
    rw [hfr, union_comm]
    exact componentIn_disjoint_closed_union hBc hAc hB.2 hd.symm hz

end PoincareConjecture.Topology.FiberSaturation
