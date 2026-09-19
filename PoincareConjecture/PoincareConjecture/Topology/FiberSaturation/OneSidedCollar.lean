import PoincareConjecture.Topology.FiberSaturation.ComplementaryComponent
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- A normalized two-sided collar parameter, with its existing subspace topology. -/
abbrev NeckParameter := Ioo (-1 : ℝ) 1

def neckCenter : NeckParameter := ⟨0, by norm_num⟩

/-- The exterior half of the collar, excluding its central cross-section. -/
def positiveCollar (X : Type*) : Set (X × NeckParameter) :=
  univ ×ˢ ((Subtype.val : NeckParameter → ℝ) ⁻¹' Ioo (0 : ℝ) 1)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The exterior half-collar is preconnected when the cross-section is. -/
theorem isPreconnected_positiveCollar [PreconnectedSpace X] :
    IsPreconnected (positiveCollar X) := by
  apply isPreconnected_univ.prod
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  rw [Subtype.image_preimage_coe, inter_eq_right.mpr
    (show Ioo (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 1 from fun t ht => ⟨by linarith [ht.1], ht.2⟩)]
  exact isPreconnected_Ioo

/-- Every point of the central section is approached from the exterior side. -/
theorem center_mem_closure_positiveCollar (x : X) :
    (x, neckCenter) ∈ closure (positiveCollar X) := by
  rw [positiveCollar, closure_prod_eq, closure_univ]
  refine ⟨mem_univ _, ?_⟩
  have h := (isOpen_Ioo : IsOpen (Ioo (-1 : ℝ) 1)).isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val (Ioo (0 : ℝ) 1)
  rw [← h]
  change (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1)
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  constructor <;> norm_num

/-- In an actual one-sided collar of C, contact with one complementary
component saturates the entire central fiber. The conclusion is not assumed
as a frontier condition: the only geometric input is C = {t ≤ 0} locally. -/
theorem oneSidedCollar_frontier_saturated [PreconnectedSpace X]
    {C : Set Y} {f : X × NeckParameter → Y} (hf : Topology.IsOpenEmbedding f)
    (hside : ∀ z, f z ∈ C ↔ (z.2 : ℝ) ≤ 0) {p : Y} {x : X}
    (hx : f (x, neckCenter) ∈ frontier (connectedComponentIn Cᶜ p)) :
    ∀ y : X, f (y, neckCenter) ∈ frontier (connectedComponentIn Cᶜ p) := by
  let S := f '' positiveCollar X
  have hS : IsPreconnected S :=
    isPreconnected_positiveCollar.image f hf.continuous.continuousOn
  have hSC : S ⊆ Cᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hC
    exact (not_le.mpr hz.2.1) ((hside z).mp hC)
  have hVS : range f ∩ Cᶜ ⊆ S := by
    rintro _ ⟨⟨z, rfl⟩, hz⟩
    refine ⟨z, ⟨mem_univ _, ?_, z.2.property.2⟩, rfl⟩
    exact lt_of_not_ge (fun ht => hz ((hside z).mpr ht))
  have hSD : S ⊆ connectedComponentIn Cᶜ p :=
    exterior_piece_subset_component hS hSC hf.isOpen_range
      (mem_range_self (x, neckCenter)) (frontier_subset_closure hx) hVS
  intro y
  have hlimit : f (y, neckCenter) ∈ closure S :=
    image_closure_subset_closure_image hf.continuous
      ⟨(y, neckCenter), center_mem_closure_positiveCollar y, rfl⟩
  rw [frontier_eq_closure_inter_closure]
  refine ⟨closure_mono hSD hlimit, subset_closure ?_⟩
  intro hyD
  exact (connectedComponentIn_subset Cᶜ p hyD)
    ((hside (y, neckCenter)).mpr le_rfl)

end PoincareConjecture.Topology.FiberSaturation
