/-
Project-local extension of the Tau Ceti PBW development.
Released under the Apache 2.0 license in LICENSE.
This file is a project addition, not claimed to be present at UPSTREAM_PIN.
See PROVENANCE.md for the source and proof-construction history.
-/
module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Multiset.Sort
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import LeeSmoothLib.External.TauCetiPBW.Algebra.Lie.UniversalEnveloping.PBW.Homogeneous
public import LeeSmoothLib.External.TauCetiPBW.Algebra.Lie.UniversalEnveloping.PBW.Ordered
public import LeeSmoothLib.External.TauCetiPBW.Algebra.Lie.UniversalEnveloping.PBW.PolyAction

/-!
# Ordered monomials as a basis of the enveloping algebra

Given a well-ordered basis of a Lie algebra, this file packages the Poincaré–Birkhoff–Witt
linear-independence statement. The remaining kernel input is
`PBWAction.act_map_lie` (the Lie identity for the Dixmier–Humphreys operators). From that
identity the ordered monomials evaluate to the commutative monomial basis, hence are linearly
independent. Combined with the already-proved spanning theorem they form a basis of `U(L)`, the
canonical map `ι` is injective, and the symmetric-algebra comparison is injective in each degree.

No appeal to Ado's theorem is used. Characteristic zero is recorded on the finite-dimensional
specialisation because the surrounding Ado development works over `ℝ`/`ℂ`; the lemmas above it
do not use `CharZero`.
-/

public section

set_option linter.unusedSectionVars false

universe u v w

open MvPolynomial Module
open TauCeti.UniversalEnvelopingAlgebra.PBWAction

namespace TauCeti.UniversalEnvelopingAlgebra

variable {R : Type u} {L : Type v} {ι : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LinearOrder ι] [WellFoundedLT ι]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

noncomputable section

/-- Sorted word attached to a multi-index. -/
def multiIndexToList (α : ι →₀ ℕ) : List ι :=
  (Finsupp.toMultiset α).sort (· ≤ ·)

theorem multiIndexToList_pairwise (α : ι →₀ ℕ) :
    (multiIndexToList α).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort (Finsupp.toMultiset α) (· ≤ ·)

theorem multiIndexToList_length (α : ι →₀ ℕ) :
    (multiIndexToList α).length = multiDeg α := by
  simp [multiIndexToList, Finsupp.card_toMultiset, multiDeg, Finsupp.degree_apply, Finsupp.sum]

/-- Ordered PBW monomial of a multi-index in a well-ordered basis. -/
def orderedBasisMonomial (b : Basis ι R L) (α : ι →₀ ℕ) : U :=
  pbwMonomial R L (fun i => b i) (multiIndexToList α)

theorem orderedBasisMonomial_mem (b : Basis ι R L) (α : ι →₀ ℕ) :
    orderedBasisMonomial b α ∈ orderedPBWMonomials R L (fun i => b i) (multiDeg α) :=
  pbwMonomial_mem_orderedPBWMonomials R L (fun i => b i)
    (multiIndexToList_pairwise α) (by simp [multiIndexToList_length])

/-- Lie homomorphism `L → gl(R[ι])` packaged from the polynomial action. -/
def polyLieHom (b : Basis ι R L) :
    L →ₗ⁅R⁆ Module.End R (MvPolynomial ι R) :=
  { act b with
    map_lie' := fun {x y} => (act_map_lie b x y).symm }

/-- Representation of the enveloping algebra on the polynomial ring. -/
def polyRepresentation (b : Basis ι R L) :
    U →ₐ[R] Module.End R (MvPolynomial ι R) :=
  _root_.UniversalEnvelopingAlgebra.lift R (polyLieHom b)

theorem polyRepresentation_ι (b : Basis ι R L) (x : L) :
    polyRepresentation b (_root_.UniversalEnvelopingAlgebra.ι R x) = act b x :=
  _root_.UniversalEnvelopingAlgebra.lift_ι_apply R (polyLieHom b) x

/-- Evaluation of the polynomial representation at `1`. -/
def evalAtOne (b : Basis ι R L) : U →ₗ[R] MvPolynomial ι R where
  toFun u := polyRepresentation b u 1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem evalAtOne_ι (b : Basis ι R L) (x : L) :
    evalAtOne b (_root_.UniversalEnvelopingAlgebra.ι R x) = act b x 1 := by
  change polyRepresentation b (_root_.UniversalEnvelopingAlgebra.ι R x) 1 = act b x 1
  rw [polyRepresentation_ι]

theorem evalAtOne_ι_basis (b : Basis ι R L) (j : ι) :
    evalAtOne b (_root_.UniversalEnvelopingAlgebra.ι R (b j)) = MvPolynomial.X j := by
  rw [evalAtOne_ι, act_basis, actBasis_one]

theorem evalAtOne_mul_ι (b : Basis ι R L) (x : L) (u : U) :
    evalAtOne b (_root_.UniversalEnvelopingAlgebra.ι R x * u) =
      act b x (evalAtOne b u) := by
  change polyRepresentation b (_root_.UniversalEnvelopingAlgebra.ι R x * u) 1 =
    act b x (polyRepresentation b u 1)
  rw [map_mul, Module.End.mul_apply, polyRepresentation_ι]

private theorem evalAtOne_one (b : Basis ι R L) : evalAtOne b 1 = 1 := by
  show polyRepresentation b (1 : U) (1 : MvPolynomial ι R) = 1
  have h := map_one (polyRepresentation b)
  have h' :=
    congrArg (fun f : Module.End R (MvPolynomial ι R) => f (1 : MvPolynomial ι R)) h
  exact h'.trans (LinearMap.id_apply (1 : MvPolynomial ι R))

/-- The product of the indeterminates attached to a multi-index is the corresponding monomial. -/
private theorem prod_map_X_toMultiset (α : ι →₀ ℕ) :
    (α.toMultiset.map (X : ι → MvPolynomial ι R)).prod = monomial α (1 : R) := by
  rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun b m₁ m₂ => pow_add b m₁ m₂)]
  exact prod_X_pow_eq_monomial

/-- A list of indeterminates multiplies to the monomial of its counting multi-index. -/
private theorem prod_map_X_eq_monomial (l : List ι) :
    (l.map (X : ι → MvPolynomial ι R)).prod =
      monomial (Multiset.toFinsupp (l : Multiset ι)) (1 : R) := by
  calc
    (l.map (X : ι → MvPolynomial ι R)).prod
      = ((l : Multiset ι).map (X : ι → MvPolynomial ι R)).prod := by
          rw [← Multiset.prod_coe, ← Multiset.map_coe]
    _ = ((Finsupp.toMultiset (Multiset.toFinsupp (l : Multiset ι))).map
          (X : ι → MvPolynomial ι R)).prod := by
          simp [Multiset.toFinsupp_toMultiset]
    _ = monomial (Multiset.toFinsupp (l : Multiset ι)) (1 : R) :=
      prod_map_X_toMultiset _

private theorem toFinsupp_multiIndexToList (α : ι →₀ ℕ) :
    Multiset.toFinsupp (multiIndexToList α : Multiset ι) = α := by
  simp [multiIndexToList, Multiset.sort_eq, Finsupp.toMultiset_toFinsupp]

private theorem multiIndexToList_toFinsupp (l : List ι) (hs : l.Pairwise (· ≤ ·)) :
    multiIndexToList (Multiset.toFinsupp (l : Multiset ι)) = l := by
  simp [multiIndexToList, Multiset.toFinsupp_toMultiset, Multiset.coe_sort]
  exact List.mergeSort_eq_self (· ≤ ·) hs

/-- Bridge: the product of `X` along the sorted word of `α` is the commutative monomial. -/
private theorem prod_map_X_multiIndexToList (α : ι →₀ ℕ) :
    ((multiIndexToList α).map (X : ι → MvPolynomial ι R)).prod = monomial α (1 : R) := by
  rw [prod_map_X_eq_monomial, toFinsupp_multiIndexToList]

/-- Evaluation of a nondecreasing word at `1` is the product of the corresponding indeterminates.
The inductive step is the easy Dixmier–Humphreys case: every index in the tail is `≥` the head,
so the tail multi-index is supported in `{i | head ≤ i}`. -/
private theorem evalAtOne_pbwMonomial_of_pairwise (b : Basis ι R L) (l : List ι)
    (hsorted : l.Pairwise (· ≤ ·)) :
    evalAtOne b (pbwMonomial R L (fun i => b i) l) =
      (l.map (X : ι → MvPolynomial ι R)).prod := by
  revert hsorted
  induction l with
  | nil =>
      intro _
      simp [evalAtOne_one]
  | cons j l ih =>
      intro hsorted
      cases hsorted with
      | cons hhead htail =>
          rw [pbwMonomial_cons, evalAtOne_mul_ι, act_basis, ih htail]
          match l with
          | [] =>
              rw [List.map_nil, List.prod_nil, actBasis_one]
              simp
          | k :: t =>
              rw [prod_map_X_eq_monomial, actBasis_monomial, one_smul]
              have hα :
                  Multiset.toFinsupp ((k :: t : List ι) : Multiset ι) ≠ 0 := by
                intro h0
                have hcoe : ((k :: t : List ι) : Multiset ι) = 0 := by
                  simpa [Multiset.toFinsupp_toMultiset] using
                    congrArg Finsupp.toMultiset h0
                simp at hcoe
              rw [actMonomial_easy b hα]
              · rw [List.map_cons, List.prod_cons, prod_map_X_eq_monomial]
              · apply Finset.le_min'
                intro i hi
                apply hhead
                have hms :
                    Finsupp.toMultiset
                        (Multiset.toFinsupp ((k :: t : List ι) : Multiset ι)) =
                      (k :: t : List ι) :=
                  Multiset.toFinsupp_toMultiset _
                rw [← Multiset.mem_coe, ← hms, Finsupp.mem_toMultiset]
                exact hi

/-- Evaluation of an ordered word at `1` is the corresponding commutative monomial. After
`act_map_lie`, this is the easy-case unfolding of the polynomial action along a nondecreasing
word, together with `(sort (toMultiset α)).map X |>.prod = monomial α 1`. -/
theorem evalAtOne_orderedBasisMonomial (b : Basis ι R L) (α : ι →₀ ℕ) :
    evalAtOne b (orderedBasisMonomial b α) = monomial α 1 := by
  rw [orderedBasisMonomial,
    evalAtOne_pbwMonomial_of_pairwise b _ (multiIndexToList_pairwise α),
    prod_map_X_multiIndexToList]

/-- Ordered PBW monomials in a well-ordered basis are linearly independent. -/
theorem linearIndependent_orderedBasisMonomial (b : Basis ι R L) :
    LinearIndependent R (orderedBasisMonomial (R := R) (L := L) b) := by
  refine LinearIndependent.of_comp (evalAtOne b) ?_
  have hcomp : evalAtOne b ∘ orderedBasisMonomial b =
      fun α => (monomial α 1 : MvPolynomial ι R) :=
    funext fun α => evalAtOne_orderedBasisMonomial b α
  rw [hcomp]
  exact (MvPolynomial.basisMonomials ι R).linearIndependent

/-- The canonical generators `ι : L → U(L)` are injective. This is the degree-one half of PBW. -/
theorem ι_injective (b : Basis ι R L) :
    Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R : L → U) := by
  intro x y hxy
  apply b.repr.injective
  have hx := congrArg (evalAtOne b) hxy
  rw [evalAtOne_ι, evalAtOne_ι, act_apply, act_apply] at hx
  simp_rw [actBasis_one] at hx
  have hX : LinearIndependent R fun j : ι => (X j : MvPolynomial ι R) := by
    have hfam : (fun j : ι => (X j : MvPolynomial ι R)) =
        fun j => monomial (Finsupp.single j 1) 1 := by
      funext j
      simp [X]
    rw [hfam]
    exact (MvPolynomial.basisMonomials ι R).linearIndependent.comp
      (fun j : ι => Finsupp.single j 1)
      (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0))
  have hx' :
      Finsupp.linearCombination R (fun j => (X j : MvPolynomial ι R)) (b.repr x) =
        Finsupp.linearCombination R (fun j => (X j : MvPolynomial ι R)) (b.repr y) := by
    simpa [Finsupp.linearCombination_apply] using hx
  exact hX hx'

/-- Finite-dimensional form over a characteristic-zero field. -/
theorem linearIndependent_ordered_monomials_of_finite
    {k : Type u} {L : Type v} [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [Module.Finite k L] :
    LinearIndependent k (orderedBasisMonomial (Module.finBasis k L)) :=
  linearIndependent_orderedBasisMonomial (Module.finBasis k L)

private theorem multiDeg_toFinsupp_coe (l : List ι) :
    multiDeg (Multiset.toFinsupp (l : Multiset ι)) = l.length := by
  rw [multiDeg_eq_sum, Finsupp.sum]
  simp only [Multiset.toFinsupp_apply, Multiset.toFinsupp_support]
  exact (Multiset.toFinset_sum_count_eq (l : Multiset ι)).trans (Multiset.coe_card l)

/-- Ordered PBW monomials of length at most `k` are exactly the well-ordered basis monomials of
multi-degree at most `k`. -/
theorem orderedPBWMonomials_eq_image (b : Basis ι R L) (k : ℕ) :
    orderedPBWMonomials R L (fun i => b i) k =
      orderedBasisMonomial b '' {α | multiDeg α ≤ k} := by
  ext a
  constructor
  · intro ha
    rw [mem_orderedPBWMonomials_iff] at ha
    obtain ⟨word, hsorted, hlen, rfl⟩ := ha
    refine ⟨Multiset.toFinsupp (word : Multiset ι), ?_, ?_⟩
    · simpa [multiDeg_toFinsupp_coe] using hlen
    · simp [orderedBasisMonomial, multiIndexToList_toFinsupp word hsorted]
  · rintro ⟨α, hα, rfl⟩
    exact orderedPBWMonomials_mono R L (fun i => b i) hα (orderedBasisMonomial_mem b α)

/-- Every ordered PBW monomial arises uniquely as `orderedBasisMonomial` of its counting
multi-index. -/
theorem range_orderedBasisMonomial (b : Basis ι R L) :
    Set.range (orderedBasisMonomial b) = ⋃ k, orderedPBWMonomials R L (fun i => b i) k := by
  ext a
  constructor
  · rintro ⟨α, rfl⟩
    exact Set.mem_iUnion.2 ⟨multiDeg α, orderedBasisMonomial_mem b α⟩
  · intro ha
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
    rw [mem_orderedPBWMonomials_iff] at hk
    obtain ⟨word, hsorted, -, rfl⟩ := hk
    exact ⟨Multiset.toFinsupp (word : Multiset ι), by
      simp [orderedBasisMonomial, multiIndexToList_toFinsupp word hsorted]⟩

/-- Combined with the spanning theorem for ordered words, the ordered monomials of a well-ordered
basis span `U(L)`. -/
theorem span_range_orderedBasisMonomial (b : Basis ι R L) :
    Submodule.span R (Set.range (orderedBasisMonomial b)) = ⊤ := by
  rw [range_orderedBasisMonomial]
  exact span_iUnion_orderedPBWMonomials_eq_top R L (fun i => b i) (by
    convert b.span_eq)

/-- Poincaré–Birkhoff–Witt basis: ordered monomials in a well-ordered basis of `L` are a basis of
`U(L)` as an `R`-module. Linear independence is the evaluation comparison; spanning is the
already-proved ordered-word filtration theorem. -/
noncomputable def orderedPBWBasis (b : Basis ι R L) : Basis (ι →₀ ℕ) R U :=
  Basis.mk (linearIndependent_orderedBasisMonomial b)
    (span_range_orderedBasisMonomial b).ge

@[simp]
theorem orderedPBWBasis_apply (b : Basis ι R L) (α : ι →₀ ℕ) :
    orderedPBWBasis b α = orderedBasisMonomial b α :=
  Basis.mk_apply _ _ _

/-- Evaluation at `1` is the linear equivalence sending the ordered PBW basis to the monomial
basis of the polynomial ring. This is the comparison-injectivity form of PBW. -/
theorem evalAtOne_eq_equiv (b : Basis ι R L) :
    evalAtOne b =
      ((orderedPBWBasis b).equiv (MvPolynomial.basisMonomials ι R)
        (Equiv.refl _)).toLinearMap := by
  refine (orderedPBWBasis b).ext fun α => ?_
  simp only [LinearEquiv.coe_toLinearMap]
  rw [Basis.equiv_apply, Equiv.refl_apply, orderedPBWBasis_apply,
    evalAtOne_orderedBasisMonomial, MvPolynomial.coe_basisMonomials]

theorem evalAtOne_injective (b : Basis ι R L) :
    Function.Injective (evalAtOne b) := by
  rw [evalAtOne_eq_equiv]
  exact LinearEquiv.injective _

theorem evalAtOne_bijective (b : Basis ι R L) :
    Function.Bijective (evalAtOne b) := by
  rw [evalAtOne_eq_equiv]
  exact LinearEquiv.bijective _

end

end TauCeti.UniversalEnvelopingAlgebra
