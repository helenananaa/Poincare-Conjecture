import PoincareConjecture.Topology.FiberSaturation.TorusComponents
import PoincareConjecture.Topology.FiberSaturation.Components

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set
variable {X : Type*} [TopologicalSpace X]

theorem proj_surjective (φ : X ≃ₜ X) (L : ℝ) : Function.Surjective (proj φ L) :=
  Quotient.mk_surjective

/-- The real base of an inverse-image region is periodic in both directions. -/
theorem base_shift_mem_iff (φ : X ≃ₜ X) (L : ℝ) (D : Set (Space φ L))
    (n : ℤ) (t : ℝ) :
    t + (n : ℝ) * L ∈ Prod.snd '' (proj φ L ⁻¹' D) ↔
      t ∈ Prod.snd '' (proj φ L ⁻¹' D) := by
  constructor
  · rintro ⟨p, hp, ht⟩
    refine ⟨deck φ L (-n) p, ?_, ?_⟩
    · simpa only [mem_preimage, proj_deck] using hp
    · change p.2 + ((-n : ℤ) : ℝ) * L = t
      rw [ht, Int.cast_neg]
      ring
  · rintro ⟨p, hp, ht⟩
    refine ⟨deck φ L n p, ?_, ?_⟩
    · simpa only [mem_preimage, proj_deck] using hp
    · change p.2 + (n : ℝ) * L = t + (n : ℝ) * L
      rw [ht]

/-- Openness of real components, obtained from explicit local intervals. -/
theorem isOpen_real_component {A : Set ℝ} (hA : IsOpen A) (t : ℝ) :
    IsOpen (connectedComponentIn A t) := by
  letI : LocallyConnectedSpace ℝ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr (fun x V hV => by
      obtain ⟨a, b, hx, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hV
      exact ⟨Ioo a b, hab, isOpen_Ioo, hx, ⟨⟨x, hx⟩, isPreconnected_Ioo⟩⟩)
  exact hA.connectedComponentIn

/-- Actual lifted components are open, without a local-connectivity
assumption on the fiber space. Fiber saturation does the extra work. -/
theorem lifted_component_isOpen [PreconnectedSpace X] (φ : X ≃ₜ X)
    (L : ℝ) {D : Set (Space φ L)} (hD : IsOpen D)
    (hs : FiberSaturated (proj φ L ⁻¹' D)) {p : X × ℝ}
    (hp : p ∈ proj φ L ⁻¹' D) :
    IsOpen (connectedComponentIn (proj φ L ⁻¹' D) p) := by
  rw [component_eq_univ_prod_image hs hp]
  exact isOpen_univ.prod (isOpen_real_component
    (isOpenMap_snd _ (hD.preimage (continuous_proj φ L))) p.2)

/-- A proper periodic base has holes on either side of every component. -/
theorem periodic_component_bounded {A : Set ℝ} {L : ℝ} (hL : 0 < L)
    (hproper : A ≠ univ)
    (hperiod : ∀ (n : ℤ) (t : ℝ), t+(n : ℝ)*L ∈ A ↔ t ∈ A)
    {t : ℝ} (ht : t ∈ A) :
    BddBelow (connectedComponentIn A t) ∧ BddAbove (connectedComponentIn A t) := by
  obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem A).mp hproper
  obtain ⟨m, hm⟩ := exists_int_lt ((t-z)/L)
  obtain ⟨n, hn⟩ := exists_int_gt ((t-z)/L)
  have hlow : z+(m : ℝ)*L < t := by
    have := (lt_div_iff₀ hL).mp hm
    linarith
  have hupp : t < z+(n : ℝ)*L := by
    have := (div_lt_iff₀ hL).mp hn
    linarith
  have hnot (k : ℤ) : z+(k : ℝ)*L ∉ A := fun h => hz ((hperiod k z).mp h)
  constructor
  · refine ⟨z+(m : ℝ)*L, ?_⟩
    intro s hs
    by_contra h
    have hzC := isPreconnected_connectedComponentIn.Icc_subset
      hs (mem_connectedComponentIn ht) ⟨(lt_of_not_ge h).le, hlow.le⟩
    exact hnot m (connectedComponentIn_subset A t hzC)
  · refine ⟨z+(n : ℝ)*L, ?_⟩
    intro s hs
    by_contra h
    have hzC := isPreconnected_connectedComponentIn.Icc_subset
      (mem_connectedComponentIn ht) hs ⟨hupp.le, (lt_of_not_ge h).le⟩
    exact hnot n (connectedComponentIn_subset A t hzC)

/-- Finite-strip geometry is now derived from openness, saturation and
properness of the quotient region, rather than left as a hypothesis. -/
theorem lifted_component_finite_strip [PreconnectedSpace X] (φ : X ≃ₜ X)
    {L : ℝ} (hL : 0 < L) {D : Set (Space φ L)} (hD : IsOpen D)
    (hproper : D ≠ univ) (hs : FiberSaturated (proj φ L ⁻¹' D))
    {p : X × ℝ} (hp : p ∈ proj φ L ⁻¹' D) :
    ∃ a b : ℝ, a < b ∧
      connectedComponentIn (proj φ L ⁻¹' D) p = (univ : Set X) ×ˢ Ioo a b := by
  let A : Set ℝ := Prod.snd '' (proj φ L ⁻¹' D)
  have ht : p.2 ∈ A := ⟨p, hp, rfl⟩
  have hA : A ≠ univ := by
    intro heq
    apply hproper
    apply eq_univ_of_forall
    intro z
    obtain ⟨q, rfl⟩ := proj_surjective φ L z
    have hq : q ∈ proj φ L ⁻¹' D := by
      rw [hs.eq_univ_prod_image]
      change q ∈ (univ : Set X) ×ˢ A
      rw [heq]
      exact ⟨mem_univ _, mem_univ _⟩
    exact hq
  have hbounds := periodic_component_bounded hL hA (base_shift_mem_iff φ L D) ht
  have hc : IsConnected (connectedComponentIn A p.2) :=
    ⟨⟨p.2, mem_connectedComponentIn ht⟩, isPreconnected_connectedComponentIn⟩
  have ho : IsOpen (connectedComponentIn A p.2) :=
    isOpen_real_component (isOpenMap_snd _ (hD.preimage (continuous_proj φ L))) p.2
  have hshape := open_connected_eq_Ioo ho hc hbounds.1 hbounds.2
  have hab : sInf (connectedComponentIn A p.2) < sSup (connectedComponentIn A p.2) := by
    have hpoint := mem_connectedComponentIn ht
    rw [hshape] at hpoint
    exact hpoint.1.trans hpoint.2
  refine ⟨_, _, hab, ?_⟩
  rw [component_eq_univ_prod_image hs hp]
  change (univ : Set X) ×ˢ connectedComponentIn A p.2 = _
  exact congrArg (fun S : Set ℝ => (univ : Set X) ×ˢ S) hshape

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
