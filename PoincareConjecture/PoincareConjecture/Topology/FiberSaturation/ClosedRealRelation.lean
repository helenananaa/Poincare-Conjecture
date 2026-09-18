import PoincareConjecture.Topology.FiberSaturation.AbstractBundleMappingTorus
import PoincareConjecture.Topology.FiberSaturation.TorusHausdorff

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CircleBundle
open Set Function
variable {F : Type*} [TopologicalSpace F]

/-- Closed-period representatives mapped into the actual integer-deck quotient.
The inverse twist matches the convention (x,L) identified with (φ x,0). -/
def fundamentalProjection (φ : F ≃ₜ F) (L : ℝ) :
    F × Icc (0 : ℝ) L → MappingTorus.Space φ.symm L :=
  fun p => MappingTorus.proj φ.symm L (p.1,(p.2 : ℝ))

theorem continuous_fundamentalProjection (φ : F ≃ₜ F) (L : ℝ) :
    Continuous (fundamentalProjection φ L) :=
  (MappingTorus.continuous_proj φ.symm L).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

theorem fundamentalProjection_fiber_injective (φ : F ≃ₜ F) {L : ℝ} (hL : 0 < L)
    (t : Icc (0 : ℝ) L) : Injective (fun x : F => fundamentalProjection φ L (x,t)) :=
  MappingTorus.proj_fiber_injective φ.symm hL t

theorem fundamentalProjection_endpoints (φ : F ≃ₜ F) {L : ℝ} (hL : 0 < L) (x : F) :
    fundamentalProjection φ L (x,⟨L,hL.le,le_rfl⟩) =
      fundamentalProjection φ L (φ x,⟨0,le_rfl,hL.le⟩) := by
  simpa [fundamentalProjection] using
    MappingTorus.period_endpoint_identification φ.symm L 0 (φ x)

theorem surjective_fundamentalProjection (φ : F ≃ₜ F) {L : ℝ} (hL : 0 < L) :
    Surjective (fundamentalProjection φ L) := by
  intro z
  have hz : z ∈ MappingTorus.proj φ.symm L '' ((univ : Set F) ×ˢ Icc (0 : ℝ) L) := by
    have he : MappingTorus.proj φ.symm L '' ((univ : Set F) ×ˢ Icc (0 : ℝ) L) = univ := by
      simpa only [zero_add] using MappingTorus.image_period_closedStrip φ.symm hL 0
    rw [he]
    exact mem_univ z
  obtain ⟨p,hp,hz⟩ := hz
  exact ⟨(p.1,⟨p.2,hp.2⟩),hz⟩

/-- No interior identifications are hidden by passing from a finite cylinder
with its explicit seam to the all-integer orbit quotient. -/
theorem fundamentalProjection_eq_iff_seam (φ : F ≃ₜ F) {L : ℝ} (hL : 0 < L)
    (p r : F × Icc (0 : ℝ) L) :
    fundamentalProjection φ L p = fundamentalProjection φ L r ↔ Seam φ p r := by
  rcases p with ⟨x,s⟩
  rcases r with ⟨y,t⟩
  constructor
  · intro h
    have hh : ((s : ℝ) : AddCircle L) = ((t : ℝ) : AddCircle L) :=
      congrArg (MappingTorus.circleProjection φ.symm L) h
    rcases circle_Icc_eq_or_endpoints hL s.2 t.2 hh with he | ⟨hs,ht⟩ | ⟨hs,ht⟩
    · have hst : s = t := Subtype.ext he
      subst t
      exact Or.inl (Prod.ext (fundamentalProjection_fiber_injective φ hL s h) rfl)
    · refine Or.inr (Or.inr ⟨hs,ht,?_⟩)
      have hs' : s = ⟨0,le_rfl,hL.le⟩ := Subtype.ext hs
      have ht' : t = ⟨L,hL.le,le_rfl⟩ := Subtype.ext ht
      subst s
      subst t
      exact fundamentalProjection_fiber_injective φ hL _
        (h.trans (fundamentalProjection_endpoints φ hL y))
    · refine Or.inr (Or.inl ⟨hs,ht,?_⟩)
      have hs' : s = ⟨L,hL.le,le_rfl⟩ := Subtype.ext hs
      have ht' : t = ⟨0,le_rfl,hL.le⟩ := Subtype.ext ht
      subst s
      subst t
      exact fundamentalProjection_fiber_injective φ hL _
        (h.symm.trans (fundamentalProjection_endpoints φ hL x))
  · rintro (he | ⟨hs,ht,hy⟩ | ⟨hs,ht,hx⟩)
    · exact congrArg (fundamentalProjection φ L) he
    · have hs' : s = ⟨L,hL.le,le_rfl⟩ := Subtype.ext hs
      have ht' : t = ⟨0,le_rfl,hL.le⟩ := Subtype.ext ht
      subst s
      subst t
      change y = φ x at hy
      subst y
      exact fundamentalProjection_endpoints φ hL x
    · have hs' : s = ⟨0,le_rfl,hL.le⟩ := Subtype.ext hs
      have ht' : t = ⟨L,hL.le,le_rfl⟩ := Subtype.ext ht
      subst s
      subst t
      change x = φ y at hx
      subst x
      exact (fundamentalProjection_endpoints φ hL y).symm

end PoincareConjecture.Topology.FiberSaturation.CircleBundle
