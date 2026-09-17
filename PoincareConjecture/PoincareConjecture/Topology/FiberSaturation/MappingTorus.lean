import PoincareConjecture.Topology.FiberSaturation.ProductPairing
import Mathlib.Topology.Constructions
import Mathlib.Algebra.Order.ToIntervalMod

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set
variable {X : Type*} [TopologicalSpace X]

/-- The n-th deck transformation, with a positive period required only in
geometric results. The convention is (x,t) ~ (φ x,t+L). -/
def deck (φ : X ≃ₜ X) (L : ℝ) (n : ℤ) : (X × ℝ) ≃ₜ (X × ℝ) where
  toFun p := ((φ ^ n) p.1, p.2 + (n : ℝ) * L)
  invFun p := ((φ ^ n).symm p.1, p.2 - (n : ℝ) * L)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem deck_zero (φ : X ≃ₜ X) (L : ℝ) (p : X × ℝ) :
    deck φ L 0 p = p := by simp [deck]

theorem deck_add (φ : X ≃ₜ X) (L : ℝ) (m n : ℤ) (p : X × ℝ) :
    deck φ L (m+n) p = deck φ L m (deck φ L n p) := by
  ext <;> simp [deck, zpow_add, add_mul, add_comm, add_left_comm]

/-- Orbit equivalence for all integer iterates, not only one-step gluing. -/
def orbitSetoid (φ : X ≃ₜ X) (L : ℝ) : Setoid (X × ℝ) where
  r p q := ∃ n : ℤ, deck φ L n p = q
  iseqv := {
    refl := fun p => ⟨0, deck_zero φ L p⟩
    symm := by
      rintro p q ⟨n, rfl⟩
      exact ⟨-n, by rw [← deck_add]; simp⟩
    trans := by
      rintro p q r ⟨m, rfl⟩ ⟨n, rfl⟩
      exact ⟨n + m, deck_add φ L n m p⟩ }

/-- The actual topological quotient of the infinite cylinder by deck iterates. -/
abbrev Space (φ : X ≃ₜ X) (L : ℝ) := Quotient (orbitSetoid φ L)

def proj (φ : X ≃ₜ X) (L : ℝ) : X × ℝ → Space φ L := Quotient.mk _

theorem proj_eq_iff (φ : X ≃ₜ X) (L : ℝ) (p q : X × ℝ) :
    proj φ L p = proj φ L q ↔ ∃ n : ℤ, deck φ L n p = q := Quotient.eq

@[simp] theorem proj_deck (φ : X ≃ₜ X) (L : ℝ) (n : ℤ) (p : X × ℝ) :
    proj φ L (deck φ L n p) = proj φ L p :=
  ((proj_eq_iff φ L p _).mpr ⟨n, rfl⟩).symm

theorem continuous_proj (φ : X ≃ₜ X) (L : ℝ) : Continuous (proj φ L) :=
  continuous_quotient_mk'

/-- Saturation is exactly the union of all integer deck translates. -/
theorem preimage_proj_image (φ : X ≃ₜ X) (L : ℝ) (U : Set (X × ℝ)) :
    proj φ L ⁻¹' (proj φ L '' U) = ⋃ n : ℤ, (deck φ L n) '' U := by
  ext p
  constructor
  · rintro ⟨q, hq, heq⟩
    obtain ⟨n, hn⟩ := (proj_eq_iff φ L q p).mp heq
    exact mem_iUnion.mpr ⟨n, q, hq, hn⟩
  · intro hp
    obtain ⟨n, q, hq, rfl⟩ := mem_iUnion.mp hp
    exact ⟨q, hq, (proj_deck φ L n q).symm⟩

theorem isOpenMap_proj (φ : X ≃ₜ X) (L : ℝ) : IsOpenMap (proj φ L) := by
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (proj φ L ⁻¹' (proj φ L '' U))
  rw [preimage_proj_image]
  exact isOpen_iUnion (fun n => (deck φ L n).isOpenMap U hU)

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
