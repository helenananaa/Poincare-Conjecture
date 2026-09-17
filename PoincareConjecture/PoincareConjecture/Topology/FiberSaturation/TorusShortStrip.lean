import PoincareConjecture.Topology.FiberSaturation.MappingTorus

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set
variable {X : Type*} [TopologicalSpace X]

/-- Two heights in a closed interval shorter than a positive period cannot
differ by a nonzero integer multiple of that period. -/
theorem integer_shift_zero {L a b s t : ℝ} (hL : 0 < L) (hw : b-a < L)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {n : ℤ}
    (heq : s + (n : ℝ) * L = t) : n = 0 := by
  by_contra hn
  have hcases : (1 : ℤ) ≤ n ∨ n ≤ -1 := by omega
  rcases hcases with hp | hm
  · have hp' : (1 : ℝ) ≤ n := by exact_mod_cast hp
    nlinarith [mul_le_mul_of_nonneg_right hp' hL.le, hs.1, ht.2]
  · have hm' : (n : ℝ) ≤ -1 := by exact_mod_cast hm
    nlinarith [mul_le_mul_of_nonneg_right hm' hL.le, hs.2, ht.1]

/-- No endpoint or interior identifications occur on a short closed strip. -/
theorem proj_injOn_closedStrip (φ : X ≃ₜ X) {L a b : ℝ} (hL : 0 < L)
    (hw : b-a < L) : InjOn (proj φ L) ((univ : Set X) ×ˢ Icc a b) := by
  intro p hp q hq heq
  obtain ⟨n, hn⟩ := (proj_eq_iff φ L p q).mp heq
  have ht : p.2 + (n : ℝ) * L = q.2 := congrArg Prod.snd hn
  have hz := integer_shift_zero hL hw hp.2 hq.2 ht
  simpa [hz] using hn

/-- One full period really identifies the boundary fibers via the twist. -/
theorem period_endpoint_identification (φ : X ≃ₜ X) (L a : ℝ) (x : X) :
    proj φ L (φ x, a+L) = proj φ L (x,a) := by
  simpa [deck] using proj_deck φ L 1 (x,a)

/-- Sharp criterion: a closed strip embeds set-theoretically exactly when
its width is less than one period. Nonempty fibers are needed for necessity. -/
theorem proj_injOn_closedStrip_iff [Nonempty X] (φ : X ≃ₜ X)
    {L a b : ℝ} (hL : 0 < L) :
    InjOn (proj φ L) ((univ : Set X) ×ˢ Icc a b) ↔ b-a < L := by
  refine ⟨?_, proj_injOn_closedStrip φ hL⟩
  intro hinj
  by_contra hn
  have hwidth : L ≤ b-a := le_of_not_gt hn
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have h1 : (φ x, a+L) ∈ (univ : Set X) ×ˢ Icc a b :=
    ⟨mem_univ _, by constructor <;> linarith⟩
  have h0 : (x,a) ∈ (univ : Set X) ×ˢ Icc a b :=
    ⟨mem_univ _, by constructor <;> linarith⟩
  have heq := congrArg Prod.snd (hinj h1 h0 (period_endpoint_identification φ L a x))
  change a+L = a at heq
  linarith

/-- The quotient map is a genuine open embedding on a short open strip. -/
theorem proj_isOpenEmbedding_openStrip (φ : X ≃ₜ X) {L a b : ℝ}
    (hL : 0 < L) (hw : b-a < L) :
    _root_.Topology.IsOpenEmbedding
      (fun p : ↥((univ : Set X) ×ˢ Ioo a b) => proj φ L p.1) := by
  refine .of_continuous_injective_isOpenMap
    ((continuous_proj φ L).comp continuous_subtype_val) ?_
    ((isOpenMap_proj φ L).comp (isOpen_univ.prod isOpen_Ioo).isOpenMap_subtype_val)
  intro p q heq
  apply Subtype.ext
  exact proj_injOn_closedStrip φ hL hw
    ⟨mem_univ _, p.2.2.1.le, p.2.2.2.le⟩
    ⟨mem_univ _, q.2.2.1.le, q.2.2.2.le⟩ heq

/-- Embed a short closed strip by restricting a slightly larger open one.
This proof does not assume that the quotient is Hausdorff. -/
theorem proj_isEmbedding_closedStrip (φ : X ≃ₜ X) {L a b : ℝ}
    (hL : 0 < L) (hw : b-a < L) :
    _root_.Topology.IsEmbedding
      (fun p : ↥((univ : Set X) ×ˢ Icc a b) => proj φ L p.1) := by
  let d : ℝ := (L-(b-a))/4
  have hd : 0 < d := by dsimp [d]; linarith
  have hw' : (b+d)-(a-d) < L := by dsimp [d]; linarith
  have hsub : ((univ : Set X) ×ˢ Icc a b) ⊆ univ ×ˢ Ioo (a-d) (b+d) := by
    intro p hp
    exact ⟨mem_univ _, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  exact (proj_isOpenEmbedding_openStrip φ hL hw').isEmbedding.comp
    (_root_.Topology.IsEmbedding.inclusion hsub)

/-- A short closed cylinder is homeomorphic to its actual image in the quotient. -/
def closedStripHomeomorphImage (φ : X ≃ₜ X) {L a b : ℝ}
    (hL : 0 < L) (hw : b-a < L) :
    ↥((univ : Set X) ×ˢ Icc a b) ≃ₜ
      ↥(proj φ L '' ((univ : Set X) ×ˢ Icc a b)) :=
  (proj_isEmbedding_closedStrip φ hL hw).toHomeomorph.trans
    (Homeomorph.setCongr (by
      ext q
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p.1, p.2, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p, hp⟩, rfl⟩))


/-- Adapter to the blueprint convention q(x,t+L)=q(φ x,t).
Use φ.symm as the deck twist; no change of gluing convention is implicit. -/
theorem blueprint_endpoint_convention (φ : X ≃ₜ X) (L a : ℝ) (x : X) :
    proj φ.symm L (x,a+L) = proj φ.symm L (φ x,a) := by
  simpa using period_endpoint_identification φ.symm L a (φ x)

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
