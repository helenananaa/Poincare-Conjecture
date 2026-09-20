/-
Project-local extension of the Tau Ceti PBW development.
Released under the Apache 2.0 license in LICENSE.
This file is a project addition, not claimed to be present at UPSTREAM_PIN.
See PROVENANCE.md for the source and proof-construction history.
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Prod.Lex
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Polynomial representation used for PBW independence

This file constructs, for a Lie algebra equipped with a well-ordered basis, the classical
Dixmier–Humphreys action of the basis on the polynomial ring. The action of a basis vector on a
monomial is defined by well-founded recursion on the lexicographic pair
`(total degree, acting index)`: an inversion is rewritten by the Lie bracket, and Jacobi identity
is used later to prove that the operators satisfy the Lie relations.

The construction does not use Ado's theorem.
-/

public section

set_option linter.unusedSectionVars false

universe u v w

open MvPolynomial Module

namespace TauCeti.UniversalEnvelopingAlgebra.PBWAction

variable {R : Type u} {L : Type v} {ι : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LinearOrder ι] [WellFoundedLT ι]

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

/-- Total degree of a multi-index. -/
abbrev multiDeg (α : ι →₀ ℕ) : ℕ := Finsupp.degree α

lemma multiDeg_sub_single_one {α : ι →₀ ℕ} {i : ι} (hi : α i ≠ 0) :
    multiDeg (α - Finsupp.single i 1) + 1 = multiDeg α := by
  have h := congrArg Finsupp.degree (Finsupp.sub_add_single_one_cancel hi)
  simpa [multiDeg, map_add, Finsupp.degree_single] using h

lemma multiDeg_sub_single_one_lt {α : ι →₀ ℕ} {i : ι} (hi : α i ≠ 0) :
    multiDeg (α - Finsupp.single i 1) < multiDeg α := by
  have h := multiDeg_sub_single_one hi
  have : 1 ≤ multiDeg α := by
    have hne : multiDeg α ≠ 0 := by
      intro h0
      exact hi (by
        have := (Finsupp.degree_eq_zero_iff α).1 h0
        simp [this])
    omega
  omega

/-- Recursion key: total degree, then the acting basis index. -/
def actKey (p : ι × (ι →₀ ℕ)) : ℕ ×ₗ ι :=
  toLex (multiDeg p.2, p.1)

def actRel (p q : ι × (ι →₀ ℕ)) : Prop :=
  actKey p < actKey q

instance : DecidableRel (@actRel ι _) :=
  fun p q => inferInstanceAs (Decidable (actKey p < actKey q))

lemma actRel_wf : WellFounded (@actRel ι _) :=
  InvImage.wf actKey wellFounded_lt

lemma actRel_of_multiDeg_lt {j k : ι} {α β : ι →₀ ℕ} (h : multiDeg β < multiDeg α) :
    actRel (k, β) (j, α) := by
  unfold actRel actKey
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- Auxiliary recursive data: action of basis index `p.1` on the monomial `X^{p.2}`. -/
def actMonomialF (b : Basis ι R L) :
    (p : ι × (ι →₀ ℕ)) → (∀ q, actRel q p → MvPolynomial ι R) → MvPolynomial ι R :=
  fun p rec =>
    let j := p.1
    let α := p.2
    if hα : α = 0 then
      MvPolynomial.X j
    else
      have hs : α.support.Nonempty := by
        rw [Finsupp.support_nonempty_iff]
        exact hα
      let i0 := α.support.min' hs
      if hj : j ≤ i0 then
        MvPolynomial.X j * monomial α 1
      else
        let β := α - Finsupp.single i0 1
        have hi0 : α i0 ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hs)
        have hβ : actRel (j, β) (j, α) :=
          actRel_of_multiDeg_lt (multiDeg_sub_single_one_lt hi0)
        let pβ := rec (j, β) hβ
        let lower :=
          pβ.support.sum fun γ =>
            MvPolynomial.coeff γ pβ •
              if hq : actRel (i0, γ) (j, α) then
                rec (i0, γ) hq
              else
                MvPolynomial.X i0 * monomial γ 1
        let bracket :=
          (b.repr ⁅b j, b i0⁆).sum fun k ck =>
            ck • rec (k, β) (actRel_of_multiDeg_lt (multiDeg_sub_single_one_lt hi0))
        lower + bracket

/-- Action of a basis vector on a monomial, by well-founded recursion. -/
def actMonomial (b : Basis ι R L) (j : ι) (α : ι →₀ ℕ) : MvPolynomial ι R :=
  actRel_wf.fix (actMonomialF b) (j, α)

theorem actMonomial_eq (b : Basis ι R L) (j : ι) (α : ι →₀ ℕ) :
    actMonomial b j α = actMonomialF b (j, α) fun q _ => actMonomial b q.1 q.2 := by
  unfold actMonomial
  exact WellFounded.fix_eq _ _ _

@[simp]
theorem actMonomial_zero (b : Basis ι R L) (j : ι) :
    actMonomial b j 0 = MvPolynomial.X j := by
  rw [actMonomial_eq, actMonomialF]
  simp

theorem actMonomial_easy (b : Basis ι R L) {j : ι} {α : ι →₀ ℕ}
    (hα : α ≠ 0) (hj : j ≤ α.support.min' (Finsupp.support_nonempty_iff.mpr hα)) :
    actMonomial b j α = MvPolynomial.X j * monomial α 1 := by
  rw [actMonomial_eq, actMonomialF]
  simp [hα, hj]

theorem actMonomial_hard (b : Basis ι R L) {j : ι} {α : ι →₀ ℕ}
    (hα : α ≠ 0)
    (hj : ¬ j ≤ α.support.min' (Finsupp.support_nonempty_iff.mpr hα)) :
    let i0 := α.support.min' (Finsupp.support_nonempty_iff.mpr hα)
    let β := α - Finsupp.single i0 1
    actMonomial b j α =
      (actMonomial b j β).support.sum (fun γ =>
        MvPolynomial.coeff γ (actMonomial b j β) •
          if actRel (i0, γ) (j, α) then actMonomial b i0 γ
          else MvPolynomial.X i0 * monomial γ 1) +
      (b.repr ⁅b j, b i0⁆).sum fun k ck => ck • actMonomial b k β := by
  intro i0 β
  rw [actMonomial_eq, actMonomialF]
  simp [hα, hj]
  rfl

theorem X_mul_monomial_one (j : ι) (α : ι →₀ ℕ) :
    MvPolynomial.X j * monomial α (1 : R) = monomial (Finsupp.single j 1 + α) 1 := by
  simpa using (monomial_single_add (n := j) (e := 1) (s := α) (a := (1 : R))).symm

lemma multiDeg_eq_sum (α : ι →₀ ℕ) : multiDeg α = α.sum fun _ e => e := by
  simp [multiDeg, Finsupp.degree_apply, Finsupp.sum]

lemma totalDegree_X_le (j : ι) : (X j : MvPolynomial ι R).totalDegree ≤ 1 := by
  simpa [X, Finsupp.sum_single_index] using
    (totalDegree_monomial_le (Finsupp.single j 1) (1 : R))

/-- The constructed action raises total degree by at most one. -/
theorem totalDegree_actMonomial_le (b : Basis ι R L) (j : ι) (α : ι →₀ ℕ) :
    (actMonomial b j α).totalDegree ≤ multiDeg α + 1 := by
  refine (actRel_wf.induction (C := fun p =>
      (actMonomial b p.1 p.2).totalDegree ≤ multiDeg p.2 + 1) (j, α)) ?_
  intro p ih
  rcases p with ⟨j, α⟩
  by_cases hα : α = 0
  · subst α
    simpa using totalDegree_X_le (R := R) j
  · by_cases hj : j ≤ α.support.min' (Finsupp.support_nonempty_iff.mpr hα)
    · rw [actMonomial_easy b hα hj, X_mul_monomial_one]
      refine (totalDegree_monomial_le _ _).trans ?_
      simp [multiDeg_eq_sum, Finsupp.sum_add_index, Finsupp.sum_single_index, add_comm,
        Function.id_def]
    · have hs : α.support.Nonempty := Finsupp.support_nonempty_iff.mpr hα
      let i0 := α.support.min' hs
      let β := α - Finsupp.single i0 1
      have hi0 : α i0 ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hs)
      have hsucc : multiDeg β + 1 = multiDeg α := multiDeg_sub_single_one hi0
      have hβdeg : multiDeg β < multiDeg α := Nat.lt_of_succ_le (by omega)
      have ihβ : (actMonomial b j β).totalDegree ≤ multiDeg β + 1 :=
        ih (j, β) (actRel_of_multiDeg_lt (j := j) (k := j) hβdeg)
      rw [actMonomial_hard b hα hj]
      have hlower :
          ((actMonomial b j β).support.sum fun γ =>
              MvPolynomial.coeff γ (actMonomial b j β) •
                if actRel (i0, γ) (j, α) then actMonomial b i0 γ
                else MvPolynomial.X i0 * monomial γ 1).totalDegree ≤ multiDeg α + 1 := by
        refine (totalDegree_finsetSum _ _).trans ?_
        refine Finset.sup_le ?_
        intro γ hγ
        refine (totalDegree_smul_le _ _).trans ?_
        have hγdeg : multiDeg γ ≤ multiDeg β + 1 :=
          ((le_totalDegree hγ).trans ihβ).trans_eq (by simp [multiDeg_eq_sum])
        have hγα : multiDeg γ ≤ multiDeg α := by
          have := hsucc
          omega
        split_ifs with hq
        · have hih : (actMonomial b i0 γ).totalDegree ≤ multiDeg γ + 1 := ih (i0, γ) hq
          have := hsucc
          omega
        · rw [X_mul_monomial_one]
          refine (totalDegree_monomial_le _ _).trans ?_
          simp [multiDeg_eq_sum, Finsupp.sum_add_index, Finsupp.sum_single_index, add_comm,
            Function.id_def]
          exact hγα
      have hbracket :
          ((b.repr ⁅b j, b i0⁆).sum fun k ck =>
              ck • actMonomial b k β).totalDegree ≤ multiDeg α + 1 := by
        rw [Finsupp.sum]
        refine (totalDegree_finsetSum _ _).trans ?_
        refine Finset.sup_le ?_
        intro k hk
        refine (totalDegree_smul_le _ _).trans ?_
        have hih : (actMonomial b k β).totalDegree ≤ multiDeg β + 1 :=
          ih (k, β) (actRel_of_multiDeg_lt (j := j) (k := k) hβdeg)
        have := hsucc
        omega
      exact (totalDegree_add _ _).trans (max_le hlower hbracket)

/-- Linear extension of `actMonomial` from monomials to polynomials. -/
def actBasis (b : Basis ι R L) (j : ι) :
    MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  (Finsupp.linearCombination R fun α => actMonomial b j α).comp
    (AddMonoidAlgebra.coeffLinearEquiv R (S := R) (M := ι →₀ ℕ)).toLinearMap

theorem actBasis_monomial (b : Basis ι R L) (j : ι) (α : ι →₀ ℕ) (c : R) :
    actBasis b j (monomial α c) = c • actMonomial b j α := by
  simp [actBasis, monomial, AddMonoidAlgebra.coeff_single]

theorem actBasis_X (b : Basis ι R L) (j k : ι) :
    actBasis b j (MvPolynomial.X k) = actMonomial b j (Finsupp.single k 1) := by
  simp [X, actBasis_monomial]

/-- Action of a general Lie-algebra element, determined by the basis. -/
def act (b : Basis ι R L) :
    L →ₗ[R] MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  b.constr R (actBasis b)

theorem act_basis (b : Basis ι R L) (j : ι) :
    act b (b j) = actBasis b j :=
  b.constr_basis R (actBasis b) j

theorem act_apply (b : Basis ι R L) (x : L) (p : MvPolynomial ι R) :
    act b x p = (b.repr x).sum fun j c => c • actBasis b j p := by
  simp [act, Basis.constr_apply]

theorem act_monomial (b : Basis ι R L) (x : L) (α : ι →₀ ℕ) (c : R) :
    act b x (monomial α c) =
      (b.repr x).sum fun j a => a • (c • actMonomial b j α) := by
  simp [act_apply, actBasis_monomial]

theorem actBasis_apply (b : Basis ι R L) (j : ι) (p : MvPolynomial ι R) :
    actBasis b j p = p.support.sum fun α => MvPolynomial.coeff α p • actMonomial b j α := by
  simp [actBasis, Finsupp.linearCombination_apply, Finsupp.sum]
  rfl

lemma actRel_of_mem_actMonomial_support (b : Basis ι R L) {j i0 : ι} {α β γ : ι →₀ ℕ}
    (hγ : γ ∈ (actMonomial b j β).support) (hdeg : multiDeg β + 1 ≤ multiDeg α)
    (hi : i0 < j) : actRel (i0, γ) (j, α) := by
  have hγdeg : multiDeg γ ≤ multiDeg β + 1 :=
    ((le_totalDegree hγ).trans (totalDegree_actMonomial_le b j β)).trans_eq
      (by simp [multiDeg_eq_sum])
  have hle : multiDeg γ ≤ multiDeg α := hγdeg.trans hdeg
  unfold actRel actKey
  rw [Prod.Lex.toLex_lt_toLex]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hi⟩

theorem actBasis_one (b : Basis ι R L) (j : ι) :
    actBasis b j 1 = MvPolynomial.X j := by
  rw [one_def, actBasis_monomial, actMonomial_zero, one_smul]

theorem totalDegree_actBasis_le (b : Basis ι R L) (j : ι) (p : MvPolynomial ι R) :
    (actBasis b j p).totalDegree ≤ p.totalDegree + 1 := by
  rw [actBasis_apply]
  refine (totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le ?_
  intro α hα
  refine (totalDegree_smul_le _ _).trans ?_
  have hαdeg : multiDeg α ≤ p.totalDegree := by
    simpa [multiDeg_eq_sum] using le_totalDegree hα
  have := totalDegree_actMonomial_le b j α
  omega

theorem totalDegree_act_le (b : Basis ι R L) (x : L) (p : MvPolynomial ι R) :
    (act b x p).totalDegree ≤ p.totalDegree + 1 := by
  rw [act_apply, Finsupp.sum]
  refine (totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le ?_
  intro j _
  exact (totalDegree_smul_le _ _).trans (totalDegree_actBasis_le b j p)

/-- In every hard-case support term the recursive fallback is unreachable: the
total-degree bound and `t < j` give `actRel (t, γ) (j, α)`. -/
theorem actMonomial_hard_eq (b : Basis ι R L) {j : ι} {α : ι →₀ ℕ}
    (hα : α ≠ 0)
    (hj : ¬ j ≤ α.support.min' (Finsupp.support_nonempty_iff.mpr hα)) :
    let i0 := α.support.min' (Finsupp.support_nonempty_iff.mpr hα)
    let β := α - Finsupp.single i0 1
    actMonomial b j α =
      actBasis b i0 (actMonomial b j β) +
      act b ⁅b j, b i0⁆ (monomial β 1) := by
  intro i0 β
  have hs : α.support.Nonempty := Finsupp.support_nonempty_iff.mpr hα
  have hi0 : α i0 ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hs)
  have hi : i0 < j := lt_of_not_ge hj
  have hdeg : multiDeg β + 1 ≤ multiDeg α := (multiDeg_sub_single_one hi0).le
  have hrel : ∀ γ ∈ (actMonomial b j β).support, actRel (i0, γ) (j, α) :=
    fun γ hγ => actRel_of_mem_actMonomial_support b hγ hdeg hi
  rw [actMonomial_hard b hα hj, actBasis_apply, act_monomial]
  simp_rw [one_smul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  rw [if_pos (hrel γ hγ)]

private lemma single_one_ne_zero (j : ι) : Finsupp.single j (1 : ℕ) ≠ 0 :=
  Finsupp.single_ne_zero.mpr (by decide)

private lemma single_one_add_ne_zero (j : ι) (α : ι →₀ ℕ) :
    Finsupp.single j (1 : ℕ) + α ≠ 0 := by
  intro h
  have hj := congrArg (fun f : ι →₀ ℕ => f j) h
  simp at hj

private lemma mem_support_single_one_add (j : ι) (α : ι →₀ ℕ) :
    j ∈ (Finsupp.single j (1 : ℕ) + α).support := by
  simp [Finsupp.mem_support_iff]

private lemma min'_single_one_add {j : ι} {α : ι →₀ ℕ}
    (h : ∀ i ∈ α.support, j ≤ i) :
    (Finsupp.single j (1 : ℕ) + α).support.min'
      (Finsupp.support_nonempty_iff.mpr (single_one_add_ne_zero j α)) = j := by
  apply le_antisymm
  · exact Finset.min'_le _ j (mem_support_single_one_add j α)
  · refine Finset.le_min' _ _ _ ?_
    intro i hi
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at hi
    split_ifs at hi with hij
    · exact hij ▸ le_rfl
    · exact h i (Finsupp.mem_support_iff.mpr (by simpa using hi))

private lemma le_of_le_support_min {j : ι} {α : ι →₀ ℕ} (hα : α ≠ 0)
    (hj : j ≤ α.support.min' (Finsupp.support_nonempty_iff.mpr hα)) :
    ∀ i ∈ α.support, j ≤ i :=
  fun i hi => hj.trans (Finset.min'_le _ i hi)

private lemma monomial_peel {α : ι →₀ ℕ} {k : ι} (hk : α k ≠ 0) :
    monomial α (1 : R) =
      MvPolynomial.X k * monomial (α - Finsupp.single k 1) 1 := by
  rw [X_mul_monomial_one, add_comm, Finsupp.sub_add_single_one_cancel hk]

private lemma single_add_sub_single (j : ι) (α : ι →₀ ℕ) :
    (Finsupp.single j (1 : ℕ) + α) - Finsupp.single j 1 = α :=
  add_tsub_cancel_left _ _

/-- Commutator defect `D_x D_y p - D_y D_x p - D_[x,y] p`. -/
private def defect (b : Basis ι R L) (x y : L) (p : MvPolynomial ι R) :
    MvPolynomial ι R :=
  act b x (act b y p) - act b y (act b x p) - act b ⁅x, y⁆ p

private def defectₗ (b : Basis ι R L) (x y : L) :
    MvPolynomial ι R →ₗ[R] MvPolynomial ι R where
  toFun p := defect b x y p
  map_add' p q := by
    simp only [defect, map_add]
    abel
  map_smul' c p := by
    simp only [defect, map_smul, RingHom.id_apply, smul_sub]

private def defectLeft (b : Basis ι R L) (y : L) (p : MvPolynomial ι R) :
    L →ₗ[R] MvPolynomial ι R where
  toFun x := defect b x y p
  map_add' x₁ x₂ := by
    simp only [defect, map_add, add_lie, LinearMap.add_apply]
    abel
  map_smul' c x := by
    simp only [defect, map_smul, smul_lie, LinearMap.smul_apply, RingHom.id_apply,
      smul_sub]

private def defectRight (b : Basis ι R L) (x : L) (p : MvPolynomial ι R) :
    L →ₗ[R] MvPolynomial ι R where
  toFun y := defect b x y p
  map_add' y₁ y₂ := by
    simp only [defect, map_add, lie_add, LinearMap.add_apply]
    abel
  map_smul' c y := by
    simp only [defect, map_smul, lie_smul, LinearMap.smul_apply, RingHom.id_apply,
      smul_sub]

private lemma defect_swap (b : Basis ι R L) (x y : L) (p : MvPolynomial ι R) :
    defect b y x p = - defect b x y p := by
  have hxy : ⁅y, x⁆ = -⁅x, y⁆ := by
    rw [← lie_skew x y, neg_neg]
  simp only [defect, hxy, map_neg, LinearMap.neg_apply]
  abel

private lemma defect_self (b : Basis ι R L) (x : L) (p : MvPolynomial ι R) :
    defect b x x p = 0 := by
  simp [defect, lie_self]

private lemma defect_eq_zero_of_basis (b : Basis ι R L) (p : MvPolynomial ι R)
    (h : ∀ i j : ι, defect b (b i) (b j) p = 0) (x y : L) :
    defect b x y p = 0 := by
  have hy : ∀ i, defectRight b (b i) p y = 0 := by
    intro i
    have hyeq : y = Finsupp.linearCombination R (b : ι → L) (b.repr y) :=
      (b.linearCombination_repr y).symm
    rw [hyeq, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_eq_zero ?_
    intro j _
    rw [map_smul]
    change (b.repr y) j • defect b (b i) (b j) p = 0
    rw [h i j, smul_zero]
  have hxeq : x = Finsupp.linearCombination R (b : ι → L) (b.repr x) :=
    (b.linearCombination_repr x).symm
  rw [show defect b x y p = defectLeft b y p x from rfl, hxeq,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero ?_
  intro i _
  rw [map_smul, show defectLeft b y p (b i) = defectRight b (b i) p y from rfl, hy i,
    smul_zero]

private lemma lie_peel (x y z : L) :
    ⁅⁅x, z⁆, y⁆ + ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ := by
  have h := lie_skew (⁅x, z⁆) y
  rw [← h, leibniz_lie x y z]
  abel

private lemma act_monomial_one (b : Basis ι R L) (j : ι) (α : ι →₀ ℕ) :
    act b (b j) (monomial α (1 : R)) = actMonomial b j α := by
  rw [act_basis, actBasis_monomial, one_smul]

private lemma act_easy_monomial (b : Basis ι R L) {j : ι} {α : ι →₀ ℕ}
    (hα : α ≠ 0)
    (hj : j ≤ α.support.min' (Finsupp.support_nonempty_iff.mpr hα)) :
    act b (b j) (monomial α (1 : R)) = monomial (Finsupp.single j 1 + α) 1 := by
  rw [act_monomial_one, actMonomial_easy b hα hj, X_mul_monomial_one]

private lemma act_zero_monomial (b : Basis ι R L) (j : ι) :
    act b (b j) (monomial (0 : ι →₀ ℕ) (1 : R)) = monomial (Finsupp.single j 1) 1 := by
  rw [← one_def, act_basis, actBasis_one, X]

/-- If `j` is a lower bound of the support of `α` (vacuous when `α = 0`) and `j < i`,
the easy unfolding of `D_j` plus the clean hard formula for `D_i` give the Lie
relation on the monomial `X^α`, with no induction. -/
private lemma defect_monomial_easy (b : Basis ι R L) {i j : ι} {α : ι →₀ ℕ}
    (hij : j < i) (hle : ∀ k ∈ α.support, j ≤ k) :
    defect b (b i) (b j) (monomial α 1) = 0 := by
  have hmin :
      (Finsupp.single j 1 + α).support.min'
        (Finsupp.support_nonempty_iff.mpr (single_one_add_ne_zero j α)) = j :=
    min'_single_one_add hle
  have hDj : act b (b j) (monomial α 1) = monomial (Finsupp.single j 1 + α) 1 := by
    by_cases hα : α = 0
    · subst α
      simpa using act_zero_monomial (R := R) (L := L) b j
    · exact act_easy_monomial b hα (hle _ (Finset.min'_mem _ (Finsupp.support_nonempty_iff.mpr hα)))
  have hαne : Finsupp.single j 1 + α ≠ 0 := single_one_add_ne_zero j α
  have hi : ¬ i ≤ (Finsupp.single j 1 + α).support.min'
      (Finsupp.support_nonempty_iff.mpr hαne) := by
    rw [hmin]
    exact not_le_of_gt hij
  have hhard := actMonomial_hard_eq b hαne hi
  -- After unfolding the `let`s, the subtracted multi-index is `α`.
  simp only at hhard
  have hsub : (Finsupp.single j 1 + α) - Finsupp.single j 1 = α :=
    single_add_sub_single j α
  -- Transport `hhard` along `min = j` and the subtraction identity.
  rw [hmin, hsub] at hhard
  -- `hhard` is now
  --   actMonomial i (single j 1 + α)
  --     = actBasis j (actMonomial i α) + act ⁅b i, b j⁆ (monomial α 1)
  unfold defect
  rw [hDj, act_monomial_one, hhard, act_basis, act_monomial_one]
  abel

private lemma rest_support_min_le {α : ι →₀ ℕ} (hα : α ≠ 0) :
    let k := α.support.min' (Finsupp.support_nonempty_iff.mpr hα)
    ∀ t ∈ (α - Finsupp.single k 1).support, k ≤ t := by
  intro k t ht
  have ht' : (α t - Finsupp.single k 1 t) ≠ 0 := by
    simpa [Finsupp.mem_support_iff, Finsupp.sub_apply] using ht
  rw [Finsupp.single_apply] at ht'
  split_ifs at ht' with htk
  · exact htk ▸ le_rfl
  · exact Finset.min'_le _ t (Finsupp.mem_support_iff.mpr ht')

private lemma act_min_rest (b : Basis ι R L) {α : ι →₀ ℕ} (hα : α ≠ 0) :
    let k := α.support.min' (Finsupp.support_nonempty_iff.mpr hα)
    let β := α - Finsupp.single k 1
    act b (b k) (monomial β 1) = monomial α 1 := by
  intro k β
  have hk : α k ≠ 0 :=
    Finsupp.mem_support_iff.mp (Finset.min'_mem _ (Finsupp.support_nonempty_iff.mpr hα))
  have hαeq : Finsupp.single k 1 + β = α := by
    rw [add_comm, Finsupp.sub_add_single_one_cancel hk]
  by_cases hβ0 : β = 0
  · rw [hβ0] at hαeq ⊢
    have : α = Finsupp.single k 1 := by simpa using hαeq.symm
    simpa [this] using act_zero_monomial (R := R) (L := L) b k
  · have hle : k ≤ β.support.min' (Finsupp.support_nonempty_iff.mpr hβ0) :=
      Finset.le_min' _ _ _ (rest_support_min_le hα)
    rw [act_easy_monomial b hβ0 hle, hαeq]

/-- Hard-case Jacobi step: `D_j(X_k q) = D_k(D_j q) + D_[j,k] q` with `k = min`
and `k < j < i`, then inner induction on index `k` together with outer induction
on `q` and the Lie Jacobi identity close the defect. -/
private lemma defect_monomial_inversion (b : Basis ι R L)
    {i j k : ι} {α β : ι →₀ ℕ}
    (hα : α ≠ 0)
    (hkdef : k = α.support.min' (Finsupp.support_nonempty_iff.mpr hα))
    (hβdef : β = α - Finsupp.single k 1)
    (hij : j < i) (hjk : k < j)
    (hinner_i : defect b (b i) (b k) (act b (b j) (monomial β 1)) = 0)
    (hinner_j : defect b (b j) (b k) (act b (b i) (monomial β 1)) = 0)
    (houter : ∀ x y : L, defect b x y (monomial β 1) = 0) :
    defect b (b i) (b j) (monomial α 1) = 0 := by
  have hj : ¬ j ≤ α.support.min' (Finsupp.support_nonempty_iff.mpr hα) := by
    rw [← hkdef]
    exact not_le_of_gt hjk
  have hi : ¬ i ≤ α.support.min' (Finsupp.support_nonempty_iff.mpr hα) := by
    rw [← hkdef]
    exact not_le_of_gt (hjk.trans hij)
  have hhardj := actMonomial_hard_eq b hα hj
  have hhardi := actMonomial_hard_eq b hα hi
  -- Unfold `let`s in the clean hard formula and rewrite min/`β`.
  simp only at hhardj hhardi
  rw [← hkdef, ← hβdef] at hhardj hhardi
  have hpq : act b (b k) (monomial β 1) = monomial α 1 := by
    simpa [hkdef, hβdef] using act_min_rest b hα
  have hDj : act b (b j) (monomial α 1) =
      act b (b k) (act b (b j) (monomial β 1)) +
        act b ⁅b j, b k⁆ (monomial β 1) := by
    rw [act_monomial_one, hhardj, act_basis, act_monomial_one]
  have hDi : act b (b i) (monomial α 1) =
      act b (b k) (act b (b i) (monomial β 1)) +
        act b ⁅b i, b k⁆ (monomial β 1) := by
    rw [act_monomial_one, hhardi, act_basis, act_monomial_one]
  -- Inner commutators on `D_j q` and `D_i q`.
  have h1 :
      act b (b i) (act b (b k) (act b (b j) (monomial β 1))) =
        act b (b k) (act b (b i) (act b (b j) (monomial β 1))) +
          act b ⁅b i, b k⁆ (act b (b j) (monomial β 1)) := by
    have := hinner_i
    simp only [defect, sub_sub, sub_eq_zero] at this
    exact this
  have h2 :
      act b (b j) (act b (b k) (act b (b i) (monomial β 1))) =
        act b (b k) (act b (b j) (act b (b i) (monomial β 1))) +
          act b ⁅b j, b k⁆ (act b (b i) (monomial β 1)) := by
    have := hinner_j
    simp only [defect, sub_sub, sub_eq_zero] at this
    exact this
  -- Expand the defect and identify it with lower-degree defects plus Jacobi.
  unfold defect
  rw [hDj, hDi]
  simp only [map_add]
  rw [h1, h2, ← hpq]
  trans
    act b (b k) (defect b (b i) (b j) (monomial β 1)) +
      defect b ⁅b i, b k⁆ (b j) (monomial β 1) +
      defect b (b i) ⁅b j, b k⁆ (monomial β 1) -
      defect b ⁅b i, b j⁆ (b k) (monomial β 1)
  · simp only [defect, map_sub]
    have hjac : ⁅⁅b i, b k⁆, b j⁆ + ⁅b i, ⁅b j, b k⁆⁆ = ⁅⁅b i, b j⁆, b k⁆ :=
      lie_peel (b i) (b j) (b k)
    rw [← sub_eq_zero]
    convert_to
        act b ⁅⁅b i, b k⁆, b j⁆ (monomial β 1) +
            act b ⁅b i, ⁅b j, b k⁆⁆ (monomial β 1) -
            act b ⁅⁅b i, b j⁆, b k⁆ (monomial β 1) = 0 using 1
    · abel
    · rw [← LinearMap.add_apply, ← map_add (act b), hjac, sub_self]
  · simp [houter]

private lemma monomial_eq_smul_one (α : ι →₀ ℕ) (c : R) :
    monomial α c = c • monomial α (1 : R) := by
  simp [smul_monomial]

private lemma multiDeg_le_of_mem_support {p : MvPolynomial ι R} {α : ι →₀ ℕ}
    (hα : α ∈ p.support) : multiDeg α ≤ p.totalDegree := by
  simpa [multiDeg_eq_sum] using le_totalDegree hα

private lemma totalDegree_monomial_one_le (α : ι →₀ ℕ) :
    (monomial α (1 : R)).totalDegree ≤ multiDeg α := by
  simpa [multiDeg_eq_sum, Function.id_def] using
    totalDegree_monomial_le (R := R) α (1 : R)

/-- **Lie identity for the Dixmier–Humphreys operators.** The constructed
operators `act b : L → End(R[ι])` are a Lie homomorphism. This is the Jacobi
resolution of the length-two rewriting overlaps (`i > t` and `j > t` on a
monomial with least index `t`). Once this identity is available,
`UniversalEnvelopingAlgebra.lift` produces a representation of `U(L)` on the
polynomial ring, and evaluation at `1` sends ordered monomials to the monomial
basis of `MvPolynomial`, proving linear independence.

The operators, their well-founded definition, the easy/hard unfolding, the
total-degree bound, and the clean hard formula
`D_j(X_t q) = D_t(D_j q) + D_[j,t] q` are already proved above. The remaining
work is nested induction: outer strong induction on total degree, inner
well-founded induction on the smaller acting index. -/
theorem act_map_lie (b : Basis ι R L) (x y : L) :
    ⁅act b x, act b y⁆ = act b ⁅x, y⁆ := by
  refine LinearMap.ext ?_
  intro p
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply]
  have hAll : ∀ n : ℕ, ∀ (q : MvPolynomial ι R), q.totalDegree ≤ n →
      ∀ x y : L, defect b x y q = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n houter
    have houter' : ∀ q : MvPolynomial ι R, q.totalDegree < n →
        ∀ x y : L, defect b x y q = 0 := by
      intro q hq x y
      exact houter q.totalDegree hq q le_rfl x y
    have hInner : ∀ j i : ι, j < i → ∀ q, q.totalDegree ≤ n →
        defect b (b i) (b j) q = 0 := by
      intro j
      refine wellFounded_lt.induction
        (C := fun j => ∀ i, j < i → ∀ q, q.totalDegree ≤ n →
          defect b (b i) (b j) q = 0) j ?_
      intro j hinner i hij q hq
      have hmono : ∀ α : ι →₀ ℕ, multiDeg α ≤ n →
          defect b (b i) (b j) (monomial α 1) = 0 := by
        intro α hαdeg
        by_cases hα : α = 0
        · subst α
          exact defect_monomial_easy b hij (by intro t ht; simp at ht)
        · let k := α.support.min' (Finsupp.support_nonempty_iff.mpr hα)
          by_cases hle : j ≤ k
          · exact defect_monomial_easy b hij (le_of_le_support_min hα hle)
          · have hklt : k < j := lt_of_not_ge hle
            let β := α - Finsupp.single k 1
            have hi0 : α k ≠ 0 :=
              Finsupp.mem_support_iff.mp
                (Finset.min'_mem _ (Finsupp.support_nonempty_iff.mpr hα))
            have hβlt : multiDeg β < multiDeg α := multiDeg_sub_single_one_lt hi0
            have hβn : multiDeg β < n := lt_of_lt_of_le hβlt hαdeg
            have hsucc : multiDeg β + 1 = multiDeg α := multiDeg_sub_single_one hi0
            have hqlt : (monomial β (1 : R)).totalDegree < n :=
              lt_of_le_of_lt (totalDegree_monomial_one_le β) hβn
            have hDjqdeg : (act b (b j) (monomial β 1)).totalDegree ≤ n := by
              have htd := totalDegree_act_le b (b j) (monomial β 1)
              have : (monomial β (1 : R)).totalDegree ≤ multiDeg β :=
                totalDegree_monomial_one_le β
              omega
            have hDiqdeg : (act b (b i) (monomial β 1)).totalDegree ≤ n := by
              have htd := totalDegree_act_le b (b i) (monomial β 1)
              have : (monomial β (1 : R)).totalDegree ≤ multiDeg β :=
                totalDegree_monomial_one_le β
              omega
            refine defect_monomial_inversion b hα rfl rfl hij hklt ?_ ?_ ?_
            · exact hinner k hklt i (hklt.trans hij)
                (act b (b j) (monomial β 1)) hDjqdeg
            · exact hinner k hklt j hklt
                (act b (b i) (monomial β 1)) hDiqdeg
            · intro x y
              exact houter' (monomial β 1) hqlt x y
      rw [show defect b (b i) (b j) q = defectₗ b (b i) (b j) q from rfl, q.as_sum, map_sum]
      refine Finset.sum_eq_zero ?_
      intro α hαs
      have hαdeg : multiDeg α ≤ n := (multiDeg_le_of_mem_support hαs).trans hq
      rw [monomial_eq_smul_one, map_smul]
      change coeff α q • defect b (b i) (b j) (monomial α 1) = 0
      rw [hmono α hαdeg, smul_zero]
    intro q hq x y
    refine defect_eq_zero_of_basis b q ?_ x y
    intro i' j'
    rcases lt_trichotomy j' i' with hlt | heq | hgt
    · exact hInner j' i' hlt q hq
    · rw [heq]
      exact defect_self b (b i') q
    · rw [defect_swap, hInner i' j' hgt q hq, neg_zero]
  have hdef : defect b x y p = 0 := hAll p.totalDegree p le_rfl x y
  simp only [defect, sub_sub, sub_eq_zero] at hdef
  exact sub_eq_iff_eq_add.mpr (hdef.trans (add_comm _ _))

end

end TauCeti.UniversalEnvelopingAlgebra.PBWAction
