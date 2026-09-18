import PoincareConjecture.Topology.FiberSaturation.BundleMonodromy

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CircleBundle
open Set Bundle Function

/-- In one closed period, equality of circle heights permits only equality
or the two endpoint identifications. -/
theorem circle_Icc_eq_or_endpoints {L s t : ℝ} (hL : 0 < L)
    (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L)
    (heq : (s : AddCircle L) = (t : AddCircle L)) :
    s = t ∨ (s = 0 ∧ t = L) ∨ (s = L ∧ t = 0) := by
  obtain ⟨n,hn⟩ := MappingTorus.circle_eq_iff_integer_shift.mp heq
  rcases lt_trichotomy n 0 with hnneg | hnzero | hnpos
  · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hm : (n : ℝ) * L ≤ -L := by nlinarith
    exact Or.inr (Or.inr ⟨by linarith [hs.2,ht.1], by linarith [hs.2,ht.1]⟩)
  · left
    simpa [hnzero] using hn
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hm : L ≤ (n : ℝ) * L := by nlinarith
    exact Or.inr (Or.inl ⟨by linarith [hs.1,ht.2], by linarith [hs.1,ht.2]⟩)

/-- Explicit endpoint relation, independent of any bundle projection or its kernel. -/
def Seam {F : Type*} [TopologicalSpace F] {L : ℝ} (φ : F ≃ₜ F)
    (p r : F × Icc (0 : ℝ) L) : Prop :=
  p = r ∨ ((p.2 : ℝ) = L ∧ (r.2 : ℝ) = 0 ∧ r.1 = φ p.1) ∨
    ((p.2 : ℝ) = 0 ∧ (r.2 : ℝ) = L ∧ p.1 = φ r.1)

variable (F : Type*) [TopologicalSpace F] {L : ℝ}
  (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [∀ z, Nonempty (E z)]

/-- The abstract bundle projection has exactly the explicit seam relation:
there are no extra identifications in the interior or in individual fibers. -/
theorem cutMap_eq_iff_seam (hL : 0 < L) (p r : F × Icc (0 : ℝ) L) :
    cutMap F E p = cutMap F E r ↔ Seam (monodromy F E hL) p r := by
  rcases p with ⟨x,s⟩
  rcases r with ⟨y,t⟩
  constructor
  · intro h
    have hb : ((s : ℝ) : AddCircle L) = ((t : ℝ) : AddCircle L) := congrArg TotalSpace.proj h
    rcases circle_Icc_eq_or_endpoints hL s.2 t.2 hb with he | ⟨hs,ht⟩ | ⟨hs,ht⟩
    · have hst : s = t := Subtype.ext he
      subst t
      exact Or.inl (Prod.ext (cutMap_fiber_injective F E s h) rfl)
    · refine Or.inr (Or.inr ⟨hs,ht,?_⟩)
      have hs' : s = ⟨0,le_rfl,hL.le⟩ := Subtype.ext hs
      have ht' : t = ⟨L,hL.le,le_rfl⟩ := Subtype.ext ht
      subst s
      subst t
      exact cutMap_fiber_injective F E _ (h.trans (cutMap_endpoints F E hL y))
    · refine Or.inr (Or.inl ⟨hs,ht,?_⟩)
      have hs' : s = ⟨L,hL.le,le_rfl⟩ := Subtype.ext hs
      have ht' : t = ⟨0,le_rfl,hL.le⟩ := Subtype.ext ht
      subst s
      subst t
      exact cutMap_fiber_injective F E _ (h.symm.trans (cutMap_endpoints F E hL x))
  · rintro (he | ⟨hs,ht,hy⟩ | ⟨hs,ht,hx⟩)
    · exact congrArg (cutMap F E) he
    · have hs' : s = ⟨L,hL.le,le_rfl⟩ := Subtype.ext hs
      have ht' : t = ⟨0,le_rfl,hL.le⟩ := Subtype.ext ht
      subst s
      subst t
      change y = monodromy F E hL x at hy
      subst y
      exact cutMap_endpoints F E hL x
    · have hs' : s = ⟨0,le_rfl,hL.le⟩ := Subtype.ext hs
      have ht' : t = ⟨L,hL.le,le_rfl⟩ := Subtype.ext ht
      subst s
      subst t
      change x = monodromy F E hL y at hx
      subst x
      exact (cutMap_endpoints F E hL y).symm

end PoincareConjecture.Topology.FiberSaturation.CircleBundle
