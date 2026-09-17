import PoincareConjecture.Topology.FiberSaturation.CanonicalCircleProjection

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set Function
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

omit [TopologicalSpace Y] in
/-- The image of any complete cylinder is the inverse image of its circle heights. -/
theorem presentation_image_cylinder (φ : X ≃ₜ X) (L : ℝ)
    (q : X × ℝ → Y) (π : Y → AddCircle L)
    (hbase : ∀ p : X × ℝ, π (q p) = (p.2 : AddCircle L))
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) (hq : Surjective q) (A : Set ℝ) :
    q '' ((univ : Set X) ×ˢ A) = π ⁻¹' ((fun t : ℝ => (t : AddCircle L)) '' A) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp.2, (hbase p).symm⟩
  · rintro ⟨t, ht, heq⟩
    obtain ⟨p, rfl⟩ := hq y
    have hh : (p.2 : AddCircle L) = (t : AddCircle L) := (hbase p).symm.trans heq.symm
    obtain ⟨n, hn⟩ := circle_eq_iff_integer_shift.mp hh
    refine ⟨deck φ L n p, ⟨mem_univ _, ?_⟩, presentation_deck_invariant φ L q hstep n p⟩
    change p.2 + (n : ℝ) * L ∈ A
    rwa [hn]

/-- Continuous presentations are embeddings on short closed strips by compactness. -/
theorem presentation_closedStrip_embedding [CompactSpace X] [T2Space Y]
    (φ : X ≃ₜ X) {L a b : ℝ} (hL : 0 < L) (hw : b - a < L)
    (q : X × ℝ → Y) (π : Y → AddCircle L) (hq : Continuous q)
    (hbase : ∀ p : X × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : X => q (x, t)))
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) :
    _root_.Topology.IsEmbedding (fun p : ↥((univ : Set X) ×ˢ Icc a b) => q p.1) := by
  letI : CompactSpace ↥((univ : Set X) ×ˢ Icc a b) :=
    isCompact_iff_compactSpace.mp (isCompact_univ.prod isCompact_Icc)
  refine ((hq.comp continuous_subtype_val).isClosedEmbedding ?_).isEmbedding
  intro p r heq
  apply Subtype.ext
  apply proj_injOn_closedStrip φ hL hw p.2 r.2
  exact (proj_eq_iff φ L p.1 r.1).mpr
    ((presentation_eq_iff_orbit φ L q π hbase hfiber hstep p.1 r.1).mp heq)

/-- Short-strip embeddings have open images because the base projection is continuous. -/
theorem presentation_openStrip_embedding [CompactSpace X] [T2Space Y]
    (φ : X ≃ₜ X) {L a b : ℝ} (hL : 0 < L) (hw : b - a < L)
    (q : X × ℝ → Y) (π : Y → AddCircle L) (hq : Continuous q)
    (hπ : Continuous π) (hsurj : Surjective q)
    (hbase : ∀ p : X × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : X => q (x, t)))
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) :
    _root_.Topology.IsOpenEmbedding (fun p : ↥((univ : Set X) ×ˢ Ioo a b) => q p.1) := by
  have hsub : ((univ : Set X) ×ˢ Ioo a b) ⊆ univ ×ˢ Icc a b :=
    fun _ hp => ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  have he := (presentation_closedStrip_embedding φ hL hw q π hq hbase hfiber hstep).comp
    (_root_.Topology.IsEmbedding.inclusion hsub)
  refine (_root_.Topology.isOpenEmbedding_iff _).mpr ⟨he, ?_⟩
  change IsOpen (range (((univ : Set X) ×ˢ Ioo a b).restrict q))
  rw [Set.range_restrict, presentation_image_cylinder φ L q π hbase hstep hsurj]
  exact (QuotientAddGroup.isOpenMap_coe (Ioo a b) isOpen_Ioo).preimage hπ

/-- Local invertibility is derived, not required as input to a compact-fiber presentation. -/
theorem presentation_isLocalHomeomorph [CompactSpace X] [T2Space Y]
    (φ : X ≃ₜ X) {L : ℝ} (hL : 0 < L)
    (q : X × ℝ → Y) (π : Y → AddCircle L) (hq : Continuous q)
    (hπ : Continuous π) (hsurj : Surjective q)
    (hbase : ∀ p : X × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : X => q (x, t)))
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) : IsLocalHomeomorph q := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro p
  refine ⟨(univ : Set X) ×ˢ Ioo (p.2 - L/3) (p.2 + L/3), ?_, ?_⟩
  · apply (isOpen_univ.prod isOpen_Ioo).mem_nhds
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  · exact presentation_openStrip_embedding φ hL (by linarith) q π hq hπ hsurj hbase hfiber hstep

/-- Continuity and compact fibers suffice for openness of the quotient presentation. -/
theorem presentation_isOpenQuotientMap [CompactSpace X] [T2Space Y]
    (φ : X ≃ₜ X) {L : ℝ} (hL : 0 < L)
    (q : X × ℝ → Y) (π : Y → AddCircle L) (hq : Continuous q)
    (hπ : Continuous π) (hsurj : Surjective q)
    (hbase : ∀ p : X × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : X => q (x, t)))
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) : IsOpenQuotientMap q :=
  ⟨hsurj, hq, (presentation_isLocalHomeomorph φ hL q π hq hπ hsurj hbase hfiber hstep).isOpenMap⟩

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
