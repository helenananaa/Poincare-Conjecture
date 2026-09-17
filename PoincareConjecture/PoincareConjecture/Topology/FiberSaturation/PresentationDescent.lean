import PoincareConjecture.Topology.FiberSaturation.CirclePresentation

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set Function
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Descent of the supplied projection through the actual integer-orbit quotient. -/
def presentationLift (φ : X ≃ₜ X) (L : ℝ) (q : X × ℝ → Y)
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) : Space φ L → Y :=
  Quotient.lift q (by
    rintro p r ⟨n, rfl⟩
    exact (presentation_deck_invariant φ L q hstep n p).symm)

omit [TopologicalSpace Y] in
@[simp] theorem presentationLift_proj (φ : X ≃ₜ X) (L : ℝ) (q : X × ℝ → Y)
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) (p : X × ℝ) :
    presentationLift φ L q hstep (proj φ L p) = q p := rfl

/-- Continuity is obtained by the quotient universal property. -/
theorem continuous_presentationLift (φ : X ≃ₜ X) (L : ℝ) (q : X × ℝ → Y)
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) (hq : Continuous q) :
    Continuous (presentationLift φ L q hstep) :=
  ((isOpenMap_proj φ L).isQuotientMap (continuous_proj φ L)
    (proj_surjective φ L)).continuous_iff.mpr hq

/-- Openness of the supplied map descends as well. -/
theorem isOpenMap_presentationLift (φ : X ≃ₜ X) (L : ℝ) (q : X × ℝ → Y)
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) (hq : IsOpenMap q) :
    IsOpenMap (presentationLift φ L q hstep) :=
  IsOpenMap.of_comp (continuous_proj φ L) (proj_surjective φ L) hq

omit [TopologicalSpace Y] in
/-- The lift is bijective; injectivity uses the derived complete orbit relation. -/
theorem bijective_presentationLift (φ : X ≃ₜ X) (L : ℝ)
    (q : X × ℝ → Y) (π : Y → AddCircle L)
    (hbase : ∀ p : X × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : X => q (x, t)))
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) (hq : Surjective q) :
    Bijective (presentationLift φ L q hstep) := by
  constructor
  · intro u v
    induction u using Quotient.inductionOn with
    | h p =>
      induction v using Quotient.inductionOn with
      | h r =>
        intro heq
        exact Quotient.sound ((presentation_eq_iff_orbit φ L q π hbase hfiber hstep p r).mp heq)
  · intro y
    obtain ⟨p, rfl⟩ := hq y
    exact ⟨proj φ L p, rfl⟩

/-- A homeomorphism constructed from a continuous open surjective presentation.
Its input is not a preexisting homeomorphism or assumed orbit equivalence. -/
def presentationHomeomorph (φ : X ≃ₜ X) (L : ℝ)
    (q : X × ℝ → Y) (π : Y → AddCircle L)
    (hbase : ∀ p : X × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : X => q (x, t)))
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t))
    (hq : IsOpenQuotientMap q) : Space φ L ≃ₜ Y :=
  (Equiv.ofBijective (presentationLift φ L q hstep)
    (bijective_presentationLift φ L q π hbase hfiber hstep hq.surjective)).toHomeomorphOfContinuousOpen
      (continuous_presentationLift φ L q hstep hq.continuous)
      (isOpenMap_presentationLift φ L q hstep hq.isOpenMap)

@[simp] theorem presentationHomeomorph_proj (φ : X ≃ₜ X) (L : ℝ)
    (q : X × ℝ → Y) (π : Y → AddCircle L)
    (hbase : ∀ p : X × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : X => q (x, t)))
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t))
    (hq : IsOpenQuotientMap q) (p : X × ℝ) :
    presentationHomeomorph φ L q π hbase hfiber hstep hq (proj φ L p) = q p := rfl

/-- A descending homeomorphism is uniquely determined by the supplied projection. -/
theorem presentationHomeomorph_unique (φ : X ≃ₜ X) (L : ℝ)
    (q : X × ℝ → Y) (e₁ e₂ : Space φ L ≃ₜ Y)
    (h₁ : ∀ p, e₁ (proj φ L p) = q p) (h₂ : ∀ p, e₂ (proj φ L p) = q p) : e₁ = e₂ := by
  ext z
  obtain ⟨p, rfl⟩ := proj_surjective φ L z
  exact (h₁ p).trans (h₂ p).symm

/-- Set pullback commutes with the constructed coordinates; applied to an
actual frontier this avoids introducing a new saturation hypothesis. -/
theorem presentation_preimage_inverse_image (φ : X ≃ₜ X) (L : ℝ)
    (q : X × ℝ → Y) (e : Space φ L ≃ₜ Y)
    (he : ∀ p, e (proj φ L p) = q p) (A : Set Y) :
    proj φ L ⁻¹' (e.symm '' A) = q ⁻¹' A := by
  ext p
  constructor
  · rintro ⟨y, hy, hyp⟩
    have hq : q p = y := by rw [← he p, ← hyp, e.apply_symm_apply]
    change q p ∈ A
    rw [hq]
    exact hy
  · intro hp
    exact ⟨q p, hp, by rw [← he p, e.symm_apply_apply]⟩

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
