import PoincareConjecture.Topology.FiberSaturation.TorusShortStrip

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set
variable {X : Type*} [TopologicalSpace X]

/-- A closed strip of one full period covers the actual quotient. -/
theorem image_period_closedStrip (φ : X ≃ₜ X) {L : ℝ} (hL : 0 < L) (a : ℝ) :
    proj φ L '' ((univ : Set X) ×ˢ Icc a (a+L)) = univ := by
  apply eq_univ_of_forall
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    let n : ℤ := -toIcoDiv hL a p.2
    have ht : p.2 + (n : ℝ) * L = toIcoMod hL a p.2 := by
      simpa [n, zsmul_eq_mul, sub_eq_add_neg] using self_sub_toIcoDiv_zsmul hL a p.2
    refine ⟨deck φ L n p, ⟨mem_univ _, ?_⟩, proj_deck φ L n p⟩
    change p.2 + (n : ℝ) * L ∈ Icc a (a+L)
    rw [ht]
    exact Ico_subset_Icc_self (toIcoMod_mem_Ico hL a p.2)

/-- The image of a full-period open strip is dense in the quotient. -/
theorem closure_image_period_openStrip (φ : X ≃ₜ X) {L : ℝ}
    (hL : 0 < L) (a : ℝ) :
    closure (proj φ L '' ((univ : Set X) ×ˢ Ioo a (a+L))) = univ := by
  have hc : closure ((univ : Set X) ×ˢ Ioo a (a+L)) = univ ×ˢ Icc a (a+L) := by
    rw [closure_prod_eq, closure_univ, closure_Ioo (by linarith : a ≠ a+L)]
  have h := image_closure_subset_closure_image (continuous_proj φ L)
    (s := (univ : Set X) ×ˢ Ioo a (a+L))
  rw [hc, image_period_closedStrip φ hL a] at h
  exact Subset.antisymm (Set.subset_univ _) h

/-- Consequently the full-period closure has no topological frontier. -/
theorem frontier_closure_image_period_empty (φ : X ≃ₜ X) {L : ℝ}
    (hL : 0 < L) (a : ℝ) :
    frontier (closure (proj φ L '' ((univ : Set X) ×ˢ Ioo a (a+L)))) = ∅ := by
  rw [closure_image_period_openStrip φ hL a, frontier_univ]

/-- Disjointness from the first deck translate gives the non-strict bound. -/
theorem width_le_period_of_disjoint [Nonempty X] (φ : X ≃ₜ X) {L a b : ℝ}
    (hL : 0 < L)
    (hdis : Disjoint ((univ : Set X) ×ˢ Ioo a b)
      ((deck φ L 1) '' ((univ : Set X) ×ˢ Ioo a b))) : b-a ≤ L := by
  by_contra h
  have hw : L < b-a := lt_of_not_ge h
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let t : ℝ := (a+b-L)/2
  have ht : (x,t) ∈ (univ : Set X) ×ˢ Ioo a b :=
    ⟨mem_univ _, by dsimp [t]; constructor <;> linarith⟩
  have hd : deck φ L 1 (x,t) ∈ (univ : Set X) ×ˢ Ioo a b := by
    simp only [deck, Set.mem_prod, Set.mem_univ, Int.cast_one, one_mul, true_and]
    dsimp [t]
    constructor <;> linarith
  exact Set.disjoint_left.mp hdis hd ⟨(x,t), ht, rfl⟩

/-- A nonempty frontier of the closure rules out the full-period case.
This is the explicit topological hypothesis; no smooth boundary identification
is smuggled into the quotient definition. -/
theorem width_lt_period_of_disjoint_frontier_closure [Nonempty X]
    (φ : X ≃ₜ X) {L a b : ℝ} (hL : 0 < L)
    (hdis : Disjoint ((univ : Set X) ×ˢ Ioo a b)
      ((deck φ L 1) '' ((univ : Set X) ×ˢ Ioo a b)))
    (hf : (frontier (closure (proj φ L '' ((univ : Set X) ×ˢ Ioo a b)))).Nonempty) :
    b-a < L := by
  have hw := width_le_period_of_disjoint φ hL hdis
  apply lt_of_le_of_ne hw
  intro heq
  have hb : b = a+L := by linarith
  rw [hb, frontier_closure_image_period_empty φ hL a] at hf
  exact Set.not_nonempty_empty hf

/-- With that strict bound proved, the closure strip really embeds in the quotient. -/
theorem closedStrip_embeds_of_disjoint_frontier_closure [Nonempty X]
    (φ : X ≃ₜ X) {L a b : ℝ} (hL : 0 < L)
    (hdis : Disjoint ((univ : Set X) ×ˢ Ioo a b)
      ((deck φ L 1) '' ((univ : Set X) ×ˢ Ioo a b)))
    (hf : (frontier (closure (proj φ L '' ((univ : Set X) ×ˢ Ioo a b)))).Nonempty) :
    Nonempty (↥((univ : Set X) ×ˢ Icc a b) ≃ₜ
      ↥(proj φ L '' ((univ : Set X) ×ˢ Icc a b))) :=
  ⟨closedStripHomeomorphImage φ hL
    (width_lt_period_of_disjoint_frontier_closure φ hL hdis hf)⟩

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
