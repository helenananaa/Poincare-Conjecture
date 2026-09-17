import PoincareConjecture.Topology.FiberSaturation.TorusComponentImage

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set
variable {X : Type*} [TopologicalSpace X]

/-- Representatives may be chosen in a half-open period; the upper endpoint
is excluded rather than silently treated as a distinct fiber. -/
theorem image_period_halfOpenStrip (φ : X ≃ₜ X) {L : ℝ} (hL : 0 < L) (a : ℝ) :
    proj φ L '' ((univ : Set X) ×ˢ Ico a (a+L)) = univ := by
  apply eq_univ_of_forall
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    let n : ℤ := -toIcoDiv hL a p.2
    have ht : p.2 + (n : ℝ) * L = toIcoMod hL a p.2 := by
      simpa [n, zsmul_eq_mul, sub_eq_add_neg] using self_sub_toIcoDiv_zsmul hL a p.2
    refine ⟨deck φ L n p, ⟨mem_univ _, ?_⟩, proj_deck φ L n p⟩
    change p.2 + (n : ℝ) * L ∈ Ico a (a+L)
    rw [ht]
    exact toIcoMod_mem_Ico hL a p.2

/-- The projected closed strip has an explicit open complement. The proof
uses all deck translates, not just local injectivity of the projection. -/
theorem image_closedStrip_eq_compl_gap (φ : X ≃ₜ X) {L a b : ℝ}
    (hL : 0 < L) :
    proj φ L '' ((univ : Set X) ×ˢ Icc a b) =
      (proj φ L '' ((univ : Set X) ×ˢ Ioo b (a+L)))ᶜ := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
    obtain ⟨n, hn⟩ := (proj_eq_iff φ L p q).mp heq.symm
    have ht : p.2 + (n : ℝ)*L = q.2 := congrArg Prod.snd hn
    by_cases hn0 : n ≤ 0
    · have hn0' : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
      have hmul := mul_nonpos_of_nonpos_of_nonneg hn0' hL.le
      linarith [hp.2.2, hq.2.1]
    · have hn1 : (1 : ℤ) ≤ n := by omega
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hmul := mul_le_mul_of_nonneg_right hn1' hL.le
      linarith [hp.2.1, hq.2.2]
  · intro hz
    have hrep : z ∈ proj φ L '' ((univ : Set X) ×ˢ Ico a (a+L)) := by
      rw [image_period_halfOpenStrip φ hL a]
      exact mem_univ _
    obtain ⟨p, hp, rfl⟩ := hrep
    by_cases ht : p.2 ≤ b
    · exact ⟨p, ⟨mem_univ _, hp.2.1, ht⟩, rfl⟩
    · exact (hz ⟨p, ⟨mem_univ _, lt_of_not_ge ht, hp.2.2⟩, rfl⟩).elim

/-- Full-fiber closed strips have closed images, even before a Hausdorff
instance for the whole quotient has been installed. -/
theorem isClosed_image_closedStrip (φ : X ≃ₜ X) {L a b : ℝ} (hL : 0 < L) :
    IsClosed (proj φ L '' ((univ : Set X) ×ˢ Icc a b)) := by
  rw [image_closedStrip_eq_compl_gap φ hL]
  exact (isOpenMap_proj φ L _ (isOpen_univ.prod isOpen_Ioo)).isClosed_compl

/-- Projection commutes with closure for the full-fiber interval in question.
This is proved rather than inferred from continuity alone. -/
theorem closure_image_openStrip (φ : X ≃ₜ X) {L a b : ℝ} (hL : 0 < L)
    (hab : a < b) :
    closure (proj φ L '' ((univ : Set X) ×ˢ Ioo a b)) =
      proj φ L '' ((univ : Set X) ×ˢ Icc a b) := by
  apply Subset.antisymm
  · apply closure_minimal (image_mono ?_) (isClosed_image_closedStrip φ hL)
    exact prod_mono (Subset.refl _) Ioo_subset_Icc_self
  · have h := image_closure_subset_closure_image (continuous_proj φ L)
      (s := (univ : Set X) ×ˢ Ioo a b)
    rwa [closure_prod_eq, closure_univ, closure_Ioo hab.ne] at h

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
