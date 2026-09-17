import PoincareConjecture.Topology.FiberSaturation.PresentationDescent

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set Function
variable {X : Type*} [TopologicalSpace X]

/-- The actual circle-valued projection of the integer-deck quotient. -/
def circleProjection (φ : X ≃ₜ X) (L : ℝ) : Space φ L → AddCircle L :=
  Quotient.lift (fun p : X × ℝ => (p.2 : AddCircle L)) (by
    rintro p r ⟨n, rfl⟩
    apply circle_eq_iff_integer_shift.mpr
    exact ⟨n, rfl⟩)

@[simp] theorem circleProjection_proj (φ : X ≃ₜ X) (L : ℝ) (p : X × ℝ) :
    circleProjection φ L (proj φ L p) = (p.2 : AddCircle L) := rfl

/-- The circle projection is continuous by descent, not by a chosen topology. -/
theorem continuous_circleProjection (φ : X ≃ₜ X) (L : ℝ) :
    Continuous (circleProjection φ L) :=
  ((isOpenMap_proj φ L).isQuotientMap (continuous_proj φ L)
    (proj_surjective φ L)).continuous_iff.mpr
      ((AddCircle.continuous_mk' L).comp continuous_snd)

/-- At a fixed height the canonical quotient introduces no identifications. -/
theorem proj_fiber_injective (φ : X ≃ₜ X) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    Injective (fun x : X => proj φ L (x, t)) := by
  intro x y h
  exact congrArg Prod.fst (proj_injOn_closedStrip φ hL
    (by linarith : t - t < L) ⟨mem_univ _, le_rfl, le_rfl⟩
    ⟨mem_univ _, le_rfl, le_rfl⟩ h)

/-- Short-strip charts show that the actual quotient projection is locally a homeomorphism. -/
theorem proj_isLocalHomeomorph (φ : X ≃ₜ X) {L : ℝ} (hL : 0 < L) :
    IsLocalHomeomorph (proj φ L) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro p
  refine ⟨(univ : Set X) ×ˢ Ioo (p.2 - L/3) (p.2 + L/3), ?_, ?_⟩
  · apply (isOpen_univ.prod isOpen_Ioo).mem_nhds
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  · exact proj_isOpenEmbedding_openStrip φ hL (by linarith)

/-- The canonical projection provides an inhabited open quotient presentation. -/
theorem proj_isOpenQuotientMap (φ : X ≃ₜ X) (L : ℝ) :
    IsOpenQuotientMap (proj φ L) :=
  ⟨proj_surjective φ L, continuous_proj φ L, isOpenMap_proj φ L⟩

/-- Every point over a circle height has a representative at that exact real height. -/
theorem image_height_fiber (φ : X ≃ₜ X) (L t : ℝ) :
    proj φ L '' ((univ : Set X) ×ˢ ({t} : Set ℝ)) =
      circleProjection φ L ⁻¹' ({(t : AddCircle L)} : Set (AddCircle L)) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    change (p.2 : AddCircle L) = (t : AddCircle L)
    rw [show p.2 = t from hp.2]
  · intro hz
    obtain ⟨p, rfl⟩ := proj_surjective φ L z
    change (p.2 : AddCircle L) = (t : AddCircle L) at hz
    obtain ⟨n, hn⟩ := circle_eq_iff_integer_shift.mp hz
    exact ⟨deck φ L n p, ⟨mem_univ _, hn⟩, proj_deck φ L n p⟩

/-- Descent on the canonical presentation recovers the identity homeomorphism. -/
theorem canonical_presentationHomeomorph (φ : X ≃ₜ X) {L : ℝ} (hL : 0 < L) :
    presentationHomeomorph φ L (proj φ L) (circleProjection φ L)
      (circleProjection_proj φ L) (proj_fiber_injective φ hL)
      (fun x t => period_endpoint_identification φ L t x) (proj_isOpenQuotientMap φ L) =
        Homeomorph.refl (Space φ L) := by
  apply presentationHomeomorph_unique φ L (proj φ L)
  · intro p; rfl
  · intro p; rfl

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
