import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Nilpotent.Basic

/-!
Nilpotent Ado core, independent of the false exact-weight helpers in Theorem 8.49.

Class ≤ 2 is complete: on `L × 𝕜` the map
`ρ(x)(y, t) = (2⁻¹ • ⁅x, y⁆ + t • x, 0)` is a faithful representation by nilpotent
endomorphisms whenever `[[L, L], L] = 0`.

Mathlib supplies `UniversalEnvelopingAlgebra` and lower-central-series nilpotency, but
not Poincaré–Birkhoff–Witt linear independence. Unweighted truncation of `U(L)` cannot
detect class ≥ 3 commutators (they already lie in `m³`). A weighted PBW filtration whose
left ideal misses degree one remains the genuine prerequisite for arbitrary nilpotency
class. Arbitrary nonzero characters of an abelian ideal are not used.
-/

universe u𝕜 u𝔤

attribute [local instance 100] LieRing.ofAssociativeRing

open LieModule
open Module (End)

namespace LeeAdoNilpotent

variable (𝕜 : Type u𝕜) [Field 𝕜] [CharZero 𝕜]
variable (L : Type u𝔤) [LieRing L] [LieAlgebra 𝕜 L]

/-! ### Class at most two -/

/-- Class ≤ 2 means the second lower-central term vanishes: `[[L, L], L] = 0`. -/
def IsClassLETwo : Prop :=
  lowerCentralSeries 𝕜 L L 2 = ⊥

omit [CharZero 𝕜] in
lemma lie_bracket_mem_lcs_one (x y : L) :
    ⁅x, y⁆ ∈ lowerCentralSeries 𝕜 L L 1 := by
  simpa using iterate_toEnd_mem_lowerCentralSeries 𝕜 L L x y 1

omit [CharZero 𝕜] in
lemma lie_lie_eq_zero_of_class_le_two (h : IsClassLETwo 𝕜 L) (x y z : L) :
    ⁅x, ⁅y, z⁆⁆ = 0 := by
  have hyz : ⁅y, z⁆ ∈ lowerCentralSeries 𝕜 L L 1 :=
    lie_bracket_mem_lcs_one 𝕜 L y z
  have hx : ⁅x, ⁅y, z⁆⁆ ∈ lowerCentralSeries 𝕜 L L 2 := by
    simpa [lowerCentralSeries_succ] using
      LieSubmodule.lie_mem_lie (LieSubmodule.mem_top (R := 𝕜) (L := L) x) hyz
  exact (LieSubmodule.mem_bot (R := 𝕜) (L := L) _).1 (h ▸ hx)

omit [CharZero 𝕜] in
lemma nested_bracket_eq_zero_of_class_le_two (h : IsClassLETwo 𝕜 L) (x z y : L) :
    ⁅⁅x, z⁆, y⁆ = 0 := by
  have hxzy : ⁅x, ⁅z, y⁆⁆ = 0 := lie_lie_eq_zero_of_class_le_two 𝕜 L h x z y
  have hzxy : ⁅z, ⁅x, y⁆⁆ = 0 := lie_lie_eq_zero_of_class_le_two 𝕜 L h z x y
  rw [lie_lie, hxzy, hzxy, sub_zero]

omit [CharZero 𝕜] in
lemma class_le_two_of_isLieAbelian [IsLieAbelian L] : IsClassLETwo 𝕜 L := by
  have h1 : lowerCentralSeries 𝕜 L L 1 = ⊥ :=
    (trivial_iff_lower_central_eq_bot 𝕜 L L).mp inferInstance
  rw [IsClassLETwo, lowerCentralSeries_succ, h1]
  simp

/-! ### Two-step affine module `L × 𝕜` -/

/-- The linear endomorphism `ρ(x)` of `L × 𝕜` given by
`(y, t) ↦ (2⁻¹ • ⁅x, y⁆ + t • x, 0)`. -/
noncomputable def twoStepEnd (x : L) : End 𝕜 (L × 𝕜) where
  toFun p := ((2⁻¹ : 𝕜) • ⁅x, p.1⁆ + p.2 • x, 0)
  map_add' p q := by
    apply Prod.ext
    · simp [add_smul, add_assoc, add_left_comm]
    · simp
  map_smul' r p := by
    apply Prod.ext
    · simp [lie_smul, smul_add, smul_smul, mul_comm r]
    · simp

omit [CharZero 𝕜] in
@[simp]
lemma twoStepEnd_apply (x y : L) (t : 𝕜) :
    twoStepEnd 𝕜 L x (y, t) = ((2⁻¹ : 𝕜) • ⁅x, y⁆ + t • x, 0) :=
  rfl

omit [CharZero 𝕜] in
lemma twoStepEnd_apply_unit (x : L) :
    twoStepEnd 𝕜 L x (0, 1) = (x, 0) := by
  rw [twoStepEnd_apply, lie_zero, smul_zero, zero_add, one_smul]

/-- The assignment `x ↦ ρ(x)` is `𝕜`-linear for every Lie algebra. -/
noncomputable def twoStepLinear : L →ₗ[𝕜] End 𝕜 (L × 𝕜) where
  toFun := twoStepEnd 𝕜 L
  map_add' x y := by
    apply LinearMap.ext
    rintro ⟨a, t⟩
    apply Prod.ext
    · simp [twoStepEnd, add_assoc, add_left_comm]
    · simp [twoStepEnd]
  map_smul' r x := by
    apply LinearMap.ext
    rintro ⟨a, t⟩
    apply Prod.ext
    · simp [twoStepEnd, smul_lie, smul_smul, mul_comm r]
    · simp [twoStepEnd]

omit [CharZero 𝕜] in
@[simp]
lemma twoStepLinear_apply (x : L) :
    twoStepLinear 𝕜 L x = twoStepEnd 𝕜 L x :=
  rfl

omit [CharZero 𝕜] in
lemma twoStepEnd_comp_snd_zero (h : IsClassLETwo 𝕜 L) (x z y : L) (t : 𝕜) :
    twoStepEnd 𝕜 L x ((2⁻¹ : 𝕜) • ⁅z, y⁆ + t • z, 0) =
      ((t * 2⁻¹) • ⁅x, z⁆, 0) := by
  have hxzy : ⁅x, ⁅z, y⁆⁆ = 0 := lie_lie_eq_zero_of_class_le_two 𝕜 L h x z y
  simp [twoStepEnd_apply, lie_add, lie_smul, hxzy, smul_smul, mul_comm t]

lemma two_inv_add_two_inv : (2⁻¹ : 𝕜) + 2⁻¹ = 1 := by
  rw [← two_mul, mul_inv_cancel₀ two_ne_zero]

lemma twoStep_t_coeff (x z : L) (t : 𝕜) :
    (t * 2⁻¹) • ⁅x, z⁆ - (t * 2⁻¹) • ⁅z, x⁆ = t • ⁅x, z⁆ := by
  rw [← lie_skew z x, smul_neg, sub_neg_eq_add, ← two_smul 𝕜, smul_smul]
  have : (2 : 𝕜) * (t * 2⁻¹) = t := by
    rw [mul_comm t, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
  rw [this]

/-- Under class ≤ 2, `twoStepLinear` is a Lie homomorphism `L → gl(L × 𝕜)`. -/
lemma twoStepLinear_map_lie (h : IsClassLETwo 𝕜 L) (x z : L) :
    twoStepLinear 𝕜 L ⁅x, z⁆ =
      twoStepLinear 𝕜 L x * twoStepLinear 𝕜 L z -
        twoStepLinear 𝕜 L z * twoStepLinear 𝕜 L x := by
  apply LinearMap.ext
  rintro ⟨y, t⟩
  have hbr : ⁅⁅x, z⁆, y⁆ = 0 := nested_bracket_eq_zero_of_class_le_two 𝕜 L h x z y
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  simp only [twoStepLinear_apply]
  rw [twoStepEnd_apply, hbr, smul_zero, zero_add]
  rw [twoStepEnd_apply 𝕜 L z y t, twoStepEnd_comp_snd_zero 𝕜 L h x z y t]
  rw [twoStepEnd_apply 𝕜 L x y t, twoStepEnd_comp_snd_zero 𝕜 L h z x y t]
  exact Prod.ext (twoStep_t_coeff 𝕜 L x z t).symm (by simp)

noncomputable def twoStepLieHom (h : IsClassLETwo 𝕜 L) :
    L →ₗ⁅𝕜⁆ End 𝕜 (L × 𝕜) where
  toLinearMap := twoStepLinear 𝕜 L
  map_lie' := by
    intro x z
    simpa [LieRing.of_associative_ring_bracket] using twoStepLinear_map_lie 𝕜 L h x z

omit [CharZero 𝕜] in
lemma twoStepLinear_injective : Function.Injective (twoStepLinear 𝕜 L) := by
  intro x y hxy
  have hx : twoStepLinear 𝕜 L x (0, 1) = twoStepLinear 𝕜 L y (0, 1) :=
    congrArg (fun f : End 𝕜 (L × 𝕜) => f (0, 1)) hxy
  rw [twoStepLinear_apply, twoStepLinear_apply, twoStepEnd_apply_unit,
    twoStepEnd_apply_unit] at hx
  exact (Prod.mk.inj hx).1

omit [CharZero 𝕜] in
lemma twoStepEnd_mul_self (h : IsClassLETwo 𝕜 L) (x : L) :
    twoStepEnd 𝕜 L x * twoStepEnd 𝕜 L x = 0 := by
  apply LinearMap.ext
  rintro ⟨y, t⟩
  have hxxy : ⁅x, ⁅x, y⁆⁆ = 0 := lie_lie_eq_zero_of_class_le_two 𝕜 L h x x y
  rw [Module.End.mul_apply]
  simp [twoStepEnd_apply, lie_add, lie_smul, hxxy, lie_self]

omit [CharZero 𝕜] in
lemma twoStepEnd_isNilpotent (h : IsClassLETwo 𝕜 L) (x : L) :
    IsNilpotent (twoStepEnd 𝕜 L x) :=
  ⟨2, by simpa [pow_two] using twoStepEnd_mul_self 𝕜 L h x⟩

omit [CharZero 𝕜] in
lemma twoStepEnd_triple (h : IsClassLETwo 𝕜 L) (x y z : L) :
    twoStepEnd 𝕜 L x * twoStepEnd 𝕜 L y * twoStepEnd 𝕜 L z = 0 := by
  apply LinearMap.ext
  rintro ⟨w, t⟩
  have hcomp := twoStepEnd_comp_snd_zero 𝕜 L h y z w t
  rw [Module.End.mul_apply, Module.End.mul_apply]
  simp [twoStepEnd_apply, hcomp, lie_lie_eq_zero_of_class_le_two 𝕜 L h]

/-! ### Faithful finite-dimensional packaging for class ≤ 2 -/

variable [FiniteDimensional 𝕜 L]

omit [FiniteDimensional 𝕜 L] in
lemma twoStep_isFaithful (h : IsClassLETwo 𝕜 L) :
    letI : LieRingModule L (L × 𝕜) :=
      LieRingModule.compLieHom (L × 𝕜) (twoStepLieHom 𝕜 L h)
    letI : LieModule 𝕜 L (L × 𝕜) :=
      LieModule.compLieHom (L × 𝕜) (twoStepLieHom 𝕜 L h)
    LieModule.IsFaithful 𝕜 L (L × 𝕜) := by
  letI : LieRingModule L (L × 𝕜) :=
    LieRingModule.compLieHom (L × 𝕜) (twoStepLieHom 𝕜 L h)
  letI : LieModule 𝕜 L (L × 𝕜) :=
    LieModule.compLieHom (L × 𝕜) (twoStepLieHom 𝕜 L h)
  refine LieModule.IsFaithful.mk ?_
  exact twoStepLinear_injective 𝕜 L

omit [FiniteDimensional 𝕜 L] in
lemma twoStep_toEnd_isNilpotent (h : IsClassLETwo 𝕜 L) (x : L) :
    letI : LieRingModule L (L × 𝕜) :=
      LieRingModule.compLieHom (L × 𝕜) (twoStepLieHom 𝕜 L h)
    letI : LieModule 𝕜 L (L × 𝕜) :=
      LieModule.compLieHom (L × 𝕜) (twoStepLieHom 𝕜 L h)
    IsNilpotent (LieModule.toEnd 𝕜 L (L × 𝕜) x) := by
  letI : LieRingModule L (L × 𝕜) :=
    LieRingModule.compLieHom (L × 𝕜) (twoStepLieHom 𝕜 L h)
  letI : LieModule 𝕜 L (L × 𝕜) :=
    LieModule.compLieHom (L × 𝕜) (twoStepLieHom 𝕜 L h)
  exact twoStepEnd_isNilpotent 𝕜 L h x

/-- Every finite-dimensional Lie algebra of class ≤ 2 over a characteristic-zero field
admits a faithful finite-dimensional representation by nilpotent endomorphisms. -/
theorem existsFaithfulFiniteDimensionalNilpotentModule_of_class_le_two
    (h : IsClassLETwo 𝕜 L) :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule L V) (_ : LieModule 𝕜 L V),
        LieModule.IsFaithful 𝕜 L V ∧
          ∀ x : L, IsNilpotent (LieModule.toEnd 𝕜 L V x) := by
  letI : LieRingModule L (L × 𝕜) :=
    LieRingModule.compLieHom (L × 𝕜) (twoStepLieHom 𝕜 L h)
  letI : LieModule 𝕜 L (L × 𝕜) :=
    LieModule.compLieHom (L × 𝕜) (twoStepLieHom 𝕜 L h)
  refine ⟨L × 𝕜, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact twoStep_isFaithful 𝕜 L h
  · intro x
    exact twoStep_toEnd_isNilpotent 𝕜 L h x

/-- Abelian Lie algebras are class ≤ 1, so the two-step construction applies. -/
theorem existsFaithfulFiniteDimensionalNilpotentModule_of_abelian [IsLieAbelian L] :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule L V) (_ : LieModule 𝕜 L V),
        LieModule.IsFaithful 𝕜 L V ∧
          ∀ x : L, IsNilpotent (LieModule.toEnd 𝕜 L V x) :=
  existsFaithfulFiniteDimensionalNilpotentModule_of_class_le_two 𝕜 L
    (class_le_two_of_isLieAbelian 𝕜 L)

/-! ### Enveloping-algebra comparison for the class-2 module

The two-step representation lifts to `U(L)` and kills every length-3 product of
generators, while still separating points of `L`. This is the class-2 case of a
finite-codimension left ideal missing the degree-one copy of `L`. Unweighted
powers `mⁿ` cannot do the same for class ≥ 3, because nested commutators already
live in `m³`.
-/

/-- Left ideal of `T(L)` generated by pure tensors of length `n`. -/
noncomputable def tensorLengthLeftIdeal (n : ℕ) :
    Submodule (TensorAlgebra 𝕜 L) (TensorAlgebra 𝕜 L) :=
  Submodule.span (TensorAlgebra 𝕜 L)
    (Set.range fun xs : Fin n → L => TensorAlgebra.tprod 𝕜 L n xs)

omit [CharZero 𝕜] [FiniteDimensional 𝕜 L] in
lemma tprod_mem_tensorLengthLeftIdeal {n : ℕ} (xs : Fin n → L) :
    TensorAlgebra.tprod 𝕜 L n xs ∈ tensorLengthLeftIdeal 𝕜 L n :=
  Submodule.subset_span ⟨xs, rfl⟩

omit [CharZero 𝕜] [FiniteDimensional 𝕜 L] in
lemma tprod_append {n m : ℕ} (xs : Fin n → L) (ys : Fin m → L) :
    TensorAlgebra.tprod 𝕜 L (n + m) (Fin.append xs ys) =
      TensorAlgebra.tprod 𝕜 L n xs * TensorAlgebra.tprod 𝕜 L m ys := by
  simp only [TensorAlgebra.tprod_apply]
  rw [List.ofFn_comp' (Fin.append xs ys) (TensorAlgebra.ι 𝕜), List.ofFn_fin_append,
    List.map_append, List.prod_append]
  simp [Function.comp_def]

omit [CharZero 𝕜] [FiniteDimensional 𝕜 L] in
/-- The length-`n` span is a left ideal of `T(L)`: left multiplication stays inside it. -/
lemma tensorLengthLeftIdeal_smul {n : ℕ} (a : TensorAlgebra 𝕜 L) (xs : Fin n → L) :
    a * TensorAlgebra.tprod 𝕜 L n xs ∈ tensorLengthLeftIdeal 𝕜 L n :=
  Submodule.smul_mem _ a (tprod_mem_tensorLengthLeftIdeal 𝕜 L xs)

/-- Extension of the two-step representation to the universal enveloping algebra. -/
noncomputable def twoStepEnveloping (h : IsClassLETwo 𝕜 L) :
    UniversalEnvelopingAlgebra 𝕜 L →ₐ[𝕜] End 𝕜 (L × 𝕜) :=
  UniversalEnvelopingAlgebra.lift 𝕜 (twoStepLieHom 𝕜 L h)

omit [FiniteDimensional 𝕜 L] in
lemma twoStepEnveloping_ι (h : IsClassLETwo 𝕜 L) (x : L) :
    twoStepEnveloping 𝕜 L h (UniversalEnvelopingAlgebra.ι 𝕜 x) = twoStepEnd 𝕜 L x := by
  simp [twoStepEnveloping, twoStepLieHom, twoStepLinear]

omit [FiniteDimensional 𝕜 L] in
lemma twoStepEnveloping_ι_mul_three (h : IsClassLETwo 𝕜 L) (x y z : L) :
    twoStepEnveloping 𝕜 L h
        (UniversalEnvelopingAlgebra.ι 𝕜 x *
          UniversalEnvelopingAlgebra.ι 𝕜 y *
          UniversalEnvelopingAlgebra.ι 𝕜 z) = 0 := by
  simp [twoStepEnveloping, twoStepLieHom, twoStepLinear, map_mul,
    twoStepEnd_triple 𝕜 L h]

omit [FiniteDimensional 𝕜 L] in
/-- The two-step module separates points of `L` already at the enveloping-algebra level. -/
lemma twoStepEnveloping_ι_injective (h : IsClassLETwo 𝕜 L) :
    Function.Injective fun x : L =>
      twoStepEnveloping 𝕜 L h (UniversalEnvelopingAlgebra.ι 𝕜 x) := by
  intro x y hxy
  dsimp at hxy
  rw [twoStepEnveloping_ι, twoStepEnveloping_ι] at hxy
  exact twoStepLinear_injective 𝕜 L hxy

omit [FiniteDimensional 𝕜 L] in
/-- Degree-one copy of `L` is not killed by the class-2 representation, so it cannot lie
in any left ideal contained in `ker(twoStepEnveloping)`. Length-3 products do lie in that
kernel. -/
lemma iota_not_mem_ker_twoStepEnveloping (h : IsClassLETwo 𝕜 L) {x : L} (hx : x ≠ 0) :
    twoStepEnveloping 𝕜 L h (UniversalEnvelopingAlgebra.ι 𝕜 x) ≠ 0 := by
  intro h0
  rw [twoStepEnveloping_ι] at h0
  have hx0 : twoStepLinear 𝕜 L x = 0 := h0
  rw [← map_zero (twoStepLinear 𝕜 L)] at hx0
  exact hx (twoStepLinear_injective 𝕜 L hx0)

/-- Real specialisation of the class-≤-2 theorem. -/
theorem existsFaithfulFiniteDimensionalNilpotentModule_of_class_le_two_real
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (h : IsClassLETwo ℝ L) :
    ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℝ V)
      (_ : FiniteDimensional ℝ V) (_ : LieRingModule L V) (_ : LieModule ℝ L V),
        LieModule.IsFaithful ℝ L V ∧
          ∀ x : L, IsNilpotent (LieModule.toEnd ℝ L V x) := by
  simpa using existsFaithfulFiniteDimensionalNilpotentModule_of_class_le_two ℝ L h

/-- Complex specialisation of the class-≤-2 theorem. -/
theorem existsFaithfulFiniteDimensionalNilpotentModule_of_class_le_two_complex
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (h : IsClassLETwo ℂ L) :
    ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : FiniteDimensional ℂ V) (_ : LieRingModule L V) (_ : LieModule ℂ L V),
        LieModule.IsFaithful ℂ L V ∧
          ∀ x : L, IsNilpotent (LieModule.toEnd ℂ L V x) := by
  simpa using existsFaithfulFiniteDimensionalNilpotentModule_of_class_le_two ℂ L h

end LeeAdoNilpotent
