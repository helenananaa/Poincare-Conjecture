import PoincareConjecture.Topology.FiberSaturation.Ambient
import PoincareConjecture.Topology.FiberSaturation.Interval
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [PreconnectedSpace X]

/-- Connected components of a cylinder are precisely cylinders over the
base components. Only preconnectedness of the fiber is needed. -/
theorem connectedComponentIn_univ_prod {A : Set B} (x : X) {t : B} (ht : t ∈ A) :
    connectedComponentIn ((univ : Set X) ×ˢ A) (x, t) =
      univ ×ˢ connectedComponentIn A t := by
  have hp : (x, t) ∈ (univ : Set X) ×ˢ A := ⟨mem_univ _, ht⟩
  apply Subset.antisymm
  · intro p hpC
    refine ⟨mem_univ _, ?_⟩
    have hc := (isPreconnected_connectedComponentIn
      (F := (univ : Set X) ×ˢ A) (x := (x, t))).image _ continuous_snd.continuousOn
    have hsub : Prod.snd '' connectedComponentIn ((univ : Set X) ×ˢ A) (x, t) ⊆ A := by
      rintro y ⟨q, hq, rfl⟩
      exact (connectedComponentIn_subset _ _ hq).2
    exact hc.subset_connectedComponentIn
      ⟨(x, t), mem_connectedComponentIn hp, rfl⟩ hsub ⟨p, hpC, rfl⟩
  · have hc : IsPreconnected ((univ : Set X) ×ˢ connectedComponentIn A t) :=
      isPreconnected_univ.prod isPreconnected_connectedComponentIn
    exact hc.subset_connectedComponentIn ⟨mem_univ _, mem_connectedComponentIn ht⟩
      (fun _ h => ⟨h.1, connectedComponentIn_subset _ _ h.2⟩)

/-- Each component inherits saturation, proved from membership saturation
of the original region rather than assumed as a new frontier condition. -/
theorem component_eq_univ_prod_image {U : Set (X × B)}
    (hs : FiberSaturated U) {p : X × B} (hp : p ∈ U) :
    connectedComponentIn U p = univ ×ˢ connectedComponentIn (Prod.snd '' U) p.2 := by
  have heq := hs.eq_univ_prod_image
  have ht : p.2 ∈ Prod.snd '' U := ⟨p, hp, rfl⟩
  calc
    connectedComponentIn U p =
        connectedComponentIn (univ ×ˢ (Prod.snd '' U)) p := congrArg (fun S => connectedComponentIn S p) heq
    _ = univ ×ˢ connectedComponentIn (Prod.snd '' U) p.2 :=
      connectedComponentIn_univ_prod p.1 ht

/-- Consequently, the actual relative frontier of a component is saturated. -/
theorem frontier_component_fiberSaturated {U : Set (X × B)}
    (hs : FiberSaturated U) {p : X × B} (hp : p ∈ U) :
    FiberSaturated (frontier (connectedComponentIn U p)) := by
  rw [component_eq_univ_prod_image hs hp]
  exact frontier_fiberSaturated_univ_prod _

/-- For an open real parameter domain, every nonempty component of an open
saturated region has an open interval as base. -/
theorem component_open_interval {J : Set ℝ} (hJ : IsOpen J)
    {U : Set (X × J)} (hU : IsOpen U) (hs : FiberSaturated U)
    {p : X × J} (hp : p ∈ U) :
    ∃ A : Set ℝ, IsOpen A ∧ OrdConnected A ∧ A.Nonempty ∧ A ⊆ J ∧
      connectedComponentIn U p = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' A) := by
  letI : LocallyConnectedSpace ℝ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr (fun x V hV => by
      obtain ⟨a, b, hx, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hV
      exact ⟨Ioo a b, hab, isOpen_Ioo, hx, ⟨⟨x, hx⟩, isPreconnected_Ioo⟩⟩)
  letI : LocallyConnectedSpace J := hJ.locallyConnectedSpace
  let C : Set J := connectedComponentIn (Prod.snd '' U) p.2
  let A : Set ℝ := (Subtype.val : J → ℝ) '' C
  have ho : IsOpen C := (isOpenMap_snd U hU).connectedComponentIn
  have hc : IsPreconnected A :=
    isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
  have hn : A.Nonempty :=
    ⟨(p.2 : ℝ), p.2, mem_connectedComponentIn ⟨p, hp, rfl⟩, rfl⟩
  refine ⟨A, hJ.isOpenMap_subtype_val C ho, hc.ordConnected, hn, ?_, ?_⟩
  · rintro t ⟨y, _, rfl⟩
    exact y.property
  · simpa only [A, C, preimage_image_eq _ Subtype.val_injective] using
      component_eq_univ_prod_image hs hp

end PoincareConjecture.Topology.FiberSaturation
