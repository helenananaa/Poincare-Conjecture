import PoincareConjecture.Topology.FiberSaturation.SmoothEmbeddingModels
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Maps.OpenQuotient

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set Function
variable {X Y : Type*} [TopologicalSpace X]

/-- Equality in the actual additive circle detects every integer period shift. -/
theorem circle_eq_iff_integer_shift {L s t : ℝ} :
    (s : AddCircle L) = (t : AddCircle L) ↔ ∃ n : ℤ, s + (n : ℝ) * L = t := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    simp only [zsmul_eq_mul] at hn
    push_cast
    linarith
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    simp only [zsmul_eq_mul, Int.cast_neg]
    linarith

/-- One-step gluing implies invariance under all positive and negative deck iterates. -/
theorem presentation_deck_invariant (φ : X ≃ₜ X) (L : ℝ) (q : X × ℝ → Y)
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) (n : ℤ) (p : X × ℝ) :
    q (deck φ L n p) = q p := by
  have h1 (z : X × ℝ) : q (deck φ L 1 z) = q z := by
    simpa [deck] using hstep z.1 z.2
  have hm (z : X × ℝ) : q (deck φ L (-1) z) = q z := by
    have h := h1 (deck φ L (-1) z)
    rw [← deck_add] at h
    simpa using h.symm
  have hall : ∀ m : ℤ, ∀ z : X × ℝ, q (deck φ L m z) = q z := by
    intro m
    induction m using Int.induction_on with
    | zero => intro z; simp
    | succ n ih => intro z; rw [deck_add, ih, h1]
    | pred n ih => intro z; rw [sub_eq_add_neg, deck_add, ih, hm]
  exact hall n p

/-- No extra identifications: circle-height compatibility and injectivity on
individual fibers recover the full orbit equivalence from one-step gluing. -/
theorem presentation_eq_iff_orbit (φ : X ≃ₜ X) (L : ℝ)
    (q : X × ℝ → Y) (π : Y → AddCircle L)
    (hbase : ∀ p : X × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : X => q (x, t)))
    (hstep : ∀ x t, q (φ x, t + L) = q (x, t)) (p r : X × ℝ) :
    q p = q r ↔ ∃ n : ℤ, deck φ L n p = r := by
  constructor
  · intro heq
    have hc : (p.2 : AddCircle L) = (r.2 : AddCircle L) := by
      rw [← hbase p, ← hbase r, heq]
    obtain ⟨n, ht⟩ := circle_eq_iff_integer_shift.mp hc
    have hq : q (deck φ L n p) = q r :=
      (presentation_deck_invariant φ L q hstep n p).trans heq
    change q ((φ ^ n) p.1, p.2 + (n : ℝ) * L) = q (r.1, r.2) at hq
    rw [ht] at hq
    have hx : (φ ^ n) p.1 = r.1 := hfiber r.2 hq
    exact ⟨n, Prod.ext hx ht⟩
  · rintro ⟨n, rfl⟩
    exact (presentation_deck_invariant φ L q hstep n p).symm

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
