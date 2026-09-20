import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projection
import LeeSmoothLib.External.TauCetiPBW.Algebra.Lie.UniversalEnveloping.PBW.Basis
import LeeSmoothLib.Ch08.Sec08_62.AdoWeightedTruncation

/-!
The nilpotent weighted-truncation bridge.

The unrestricted positive-weight statement is false: the obstruction
`[h,e] = e` is proved in `AdoWeightedTruncation`.  Here the weights come from
the lower-central series of a genuinely nilpotent Lie algebra.  The PBW leaf
is imported from TauCeti's interface; it is not reproved in this file.

The raw high-weight ideal below is made two-sided by construction.  Its finite
codimension and derivation stability are unconditional.  The comparison of raw
high-weight words with ordered PBW monomials is proved from the lower-central
series weights below; `HighWeightOrderedRewrite` is retained as the resulting
named proposition, not as an extra hypothesis of the faithful-module theorem.
-/

universe u𝕜 u𝔤

attribute [local instance 100] LieRing.ofAssociativeRing

open scoped Pointwise Classical
open LieModule
open LeeAdoWeightedTruncation

namespace LeeNilpotentPBWWeightedBridge

variable (𝕜 : Type u𝕜) [Field 𝕜] [CharZero 𝕜]
variable (L : Type u𝔤) [LieRing L] [LieAlgebra 𝕜 L] [FiniteDimensional 𝕜 L]

local notation "U" => UniversalEnvelopingAlgebra 𝕜 L

/-! ### Lower-central-series weights -/

def lcsSub (k : ℕ) : Submodule 𝕜 L :=
  (lowerCentralSeries 𝕜 L L k).toSubmodule

lemma lcsSub_mono {i j : ℕ} (h : i ≤ j) : lcsSub 𝕜 L j ≤ lcsSub 𝕜 L i :=
  antitone_lowerCentralSeries 𝕜 L L h

lemma lcsSub_zero : lcsSub 𝕜 L 0 = ⊤ := by
  simp [lcsSub]

lemma lcsSub_succ (k : ℕ) :
    lcsSub 𝕜 L (k + 1) =
      (⁅(⊤ : LieIdeal 𝕜 L), lowerCentralSeries 𝕜 L L k⁆ :
        LieSubmodule 𝕜 L L).toSubmodule := by
  change (lowerCentralSeries 𝕜 L L (k + 1)).toSubmodule = _
  rw [lowerCentralSeries_succ]

lemma lie_lie_ideal_le_sup (I J N : LieIdeal 𝕜 L) :
    ⁅⁅I, J⁆, N⁆ ≤ ⁅I, ⁅J, N⁆⁆ ⊔ ⁅J, ⁅I, N⁆⁆ := by
  rw [LieSubmodule.lie_le_iff]
  intro x hx z hz
  have hx' : x ∈ (⁅I, J⁆ : LieIdeal 𝕜 L).toSubmodule := by
    exact hx
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx'
  refine Submodule.span_induction
    (p := fun y _ => ⁅y, z⁆ ∈ (⁅I, ⁅J, N⁆⁆ ⊔ ⁅J, ⁅I, N⁆⁆ : LieIdeal 𝕜 L))
    ?_ ?_ ?_ ?_ hx'
  · rintro y ⟨a, ha, b, hb, rfl⟩
    rw [lie_lie a b z]
    have h1 : ⁅a, ⁅b, z⁆⁆ ∈ ⁅I, ⁅J, N⁆⁆ :=
      LieSubmodule.lie_mem_lie ha (LieSubmodule.lie_mem_lie hb hz)
    have h2 : ⁅b, ⁅a, z⁆⁆ ∈ ⁅J, ⁅I, N⁆⁆ :=
      LieSubmodule.lie_mem_lie hb (LieSubmodule.lie_mem_lie ha hz)
    have h1' : ⁅a, ⁅b, z⁆⁆ ∈
        (⁅I, ⁅J, N⁆⁆ ⊔ ⁅J, ⁅I, N⁆⁆ : LieIdeal 𝕜 L) :=
      (show ⁅I, ⁅J, N⁆⁆ ≤
          (⁅I, ⁅J, N⁆⁆ ⊔ ⁅J, ⁅I, N⁆⁆ : LieIdeal 𝕜 L) from le_sup_left) h1
    have h2' : ⁅b, ⁅a, z⁆⁆ ∈
        (⁅I, ⁅J, N⁆⁆ ⊔ ⁅J, ⁅I, N⁆⁆ : LieIdeal 𝕜 L) :=
      (show ⁅J, ⁅I, N⁆⁆ ≤
          (⁅I, ⁅J, N⁆⁆ ⊔ ⁅J, ⁅I, N⁆⁆ : LieIdeal 𝕜 L) from le_sup_right) h2
    exact sub_mem h1' h2'
  · simp
  · intro u v _ _ hu hv
    rw [add_lie]
    exact add_mem hu hv
  · intro r u _ hu
    rw [smul_lie]
    exact SMulMemClass.smul_mem r hu

lemma lie_lcs_add (a b : ℕ) :
    ⁅lowerCentralSeries 𝕜 L L a, lowerCentralSeries 𝕜 L L b⁆ ≤
      lowerCentralSeries 𝕜 L L (a + b + 1) := by
  induction a generalizing b with
  | zero =>
      simp [lowerCentralSeries_zero, lowerCentralSeries_succ, add_comm]
  | succ a ih =>
      have hstep :
          ⁅lowerCentralSeries 𝕜 L L (a + 1), lowerCentralSeries 𝕜 L L b⁆ ≤
            ⁅(⊤ : LieIdeal 𝕜 L),
              ⁅lowerCentralSeries 𝕜 L L a, lowerCentralSeries 𝕜 L L b⁆⁆ ⊔
              ⁅lowerCentralSeries 𝕜 L L a,
                lowerCentralSeries 𝕜 L L (b + 1)⁆ := by
        simpa [lowerCentralSeries_succ, lowerCentralSeries_zero] using
          lie_lie_ideal_le_sup 𝕜 L (⊤ : LieIdeal 𝕜 L)
            (lowerCentralSeries 𝕜 L L a) (lowerCentralSeries 𝕜 L L b)
      have h1 :
          ⁅(⊤ : LieIdeal 𝕜 L),
              ⁅lowerCentralSeries 𝕜 L L a, lowerCentralSeries 𝕜 L L b⁆⁆ ≤
            lowerCentralSeries 𝕜 L L (a + (b + 1) + 1) := by
        have h := LieSubmodule.mono_lie_right (⊤ : LieIdeal 𝕜 L) (ih b)
        have hidx : a + (b + 1) + 1 = (a + b + 1) + 1 := by omega
        rw [hidx, lowerCentralSeries_succ]
        exact h
      have h2 :
          ⁅lowerCentralSeries 𝕜 L L a, lowerCentralSeries 𝕜 L L (b + 1)⁆ ≤
            lowerCentralSeries 𝕜 L L (a + (b + 1) + 1) := ih (b + 1)
      have hres := hstep.trans (sup_le h1 h2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hres

lemma lie_mem_lcs_add {a b : ℕ} {x y : L}
    (hx : x ∈ lcsSub 𝕜 L a) (hy : y ∈ lcsSub 𝕜 L b) :
    ⁅x, y⁆ ∈ lcsSub 𝕜 L (a + b + 1) :=
  lie_lcs_add 𝕜 L a b (LieSubmodule.lie_mem_lie hx hy)

/-! ### A basis adapted to the lower-central filtration -/

variable [LieRing.IsNilpotent L]

lemma lcs_nilpotencyLength_eq_bot :
    lowerCentralSeries 𝕜 L L (nilpotencyLength L L) = ⊥ := by
  have hs : {k | lowerCentralSeries ℤ L L k = ⊥}.Nonempty := by
    exact (LieModule.isNilpotent_iff ℤ L L).mp inferInstance
  have hℤ : lowerCentralSeries ℤ L L (nilpotencyLength L L) = ⊥ :=
    Nat.sInf_mem hs
  have hcoe := LieModule.coe_lowerCentralSeries_eq_int 𝕜 L L
    (nilpotencyLength L L)
  have hℤ' : (lowerCentralSeries ℤ L L (nilpotencyLength L L) : Set L) =
      ((⊥ : LieSubmodule ℤ L L) : Set L) := by
    simpa using congrArg (fun N : LieSubmodule ℤ L L => (N : Set L)) hℤ
  ext x
  change x ∈ (lowerCentralSeries 𝕜 L L (nilpotencyLength L L) : Set L) ↔
    x ∈ ((⊥ : LieSubmodule 𝕜 L L) : Set L)
  rw [hcoe, hℤ']
  rfl

lemma lcsSub_eq_bot_of_nilpotencyLength_le {k : ℕ}
    (h : nilpotencyLength L L ≤ k) : lcsSub 𝕜 L k = ⊥ := by
  have h0 : lcsSub 𝕜 L (nilpotencyLength L L) = ⊥ := by
    simpa [lcsSub] using (lcs_nilpotencyLength_eq_bot 𝕜 L)
  exact (le_antisymm ((lcsSub_mono 𝕜 L h).trans_eq h0) bot_le)

structure WeightedBasis (M : Type*) [AddCommGroup M] [Module 𝕜 M] where
  n : ℕ
  basis : Module.Basis (Fin n) 𝕜 M
  wt : Fin n → ℕ
  wt_pos : ∀ i, 1 ≤ wt i

noncomputable def WeightedBasis.map {M N : Type*}
    [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]
    (e : M ≃ₗ[𝕜] N) (b : WeightedBasis 𝕜 M) : WeightedBasis 𝕜 N where
  n := b.n
  basis := b.basis.map e
  wt := b.wt
  wt_pos := b.wt_pos

noncomputable def WeightedBasis.combine {M : Type*}
    [AddCommGroup M] [Module 𝕜 M]
    {p q : Submodule 𝕜 M} (h : IsCompl p q)
    (bp : WeightedBasis 𝕜 p) (bq : WeightedBasis 𝕜 q) :
    WeightedBasis 𝕜 M where
  n := bp.n + bq.n
  basis :=
    ((bp.basis.prod bq.basis).map (Submodule.prodEquivOfIsCompl p q h)).reindex
      finSumFinEquiv
  wt := fun i => Sum.elim bp.wt bq.wt (finSumFinEquiv.symm i)
  wt_pos := by
    intro i
    cases hsum : finSumFinEquiv.symm i with
    | inl a =>
        change 1 ≤ bp.wt a
        exact bp.wt_pos a
    | inr a =>
        change 1 ≤ bq.wt a
        exact bq.wt_pos a

noncomputable def WeightedBasis.ofSubsingleton (M : Type*)
    [AddCommGroup M] [Module 𝕜 M] [Subsingleton M] [FiniteDimensional 𝕜 M] :
    WeightedBasis 𝕜 M where
  n := 0
  basis := Module.Basis.empty M
  wt := Fin.elim0
  wt_pos := fun i => Fin.elim0 i

lemma WeightedBasis.ofSubsingleton_n (M : Type*)
    [AddCommGroup M] [Module 𝕜 M] [Subsingleton M] [FiniteDimensional 𝕜 M] :
    (WeightedBasis.ofSubsingleton 𝕜 M).n = 0 := rfl

noncomputable def lcsSuccComap (k : ℕ) : Submodule 𝕜 (lcsSub 𝕜 L k) :=
  (lcsSub 𝕜 L (k + 1)).comap (lcsSub 𝕜 L k).subtype

noncomputable def lcsLayerComplement (k : ℕ) : Submodule 𝕜 (lcsSub 𝕜 L k) :=
  Classical.choose (lcsSuccComap 𝕜 L k).exists_isCompl

lemma lcsLayerComplement_isCompl (k : ℕ) :
    IsCompl (lcsLayerComplement 𝕜 L k) (lcsSuccComap 𝕜 L k) :=
  (Classical.choose_spec (lcsSuccComap 𝕜 L k).exists_isCompl).symm

noncomputable def lcsLayerComplementBasis (k : ℕ) :
    WeightedBasis 𝕜 (lcsLayerComplement 𝕜 L k) where
  n := Module.finrank 𝕜 (lcsLayerComplement 𝕜 L k)
  basis := Module.finBasis 𝕜 (lcsLayerComplement 𝕜 L k)
  wt := fun _ => k + 1
  wt_pos := fun _ => Nat.succ_le_succ (Nat.zero_le _)

noncomputable def lcsSuccComap_equiv (k : ℕ) :
    lcsSuccComap 𝕜 L k ≃ₗ[𝕜] lcsSub 𝕜 L (k + 1) :=
  Submodule.comapSubtypeEquivOfLe (lcsSub_mono 𝕜 L (Nat.le_succ k))

noncomputable def lcsWeightedBasis : (k : ℕ) → WeightedBasis 𝕜 (lcsSub 𝕜 L k)
  | k =>
    if h : nilpotencyLength L L ≤ k then
      haveI : Subsingleton (lcsSub 𝕜 L k) := by
        rw [lcsSub_eq_bot_of_nilpotencyLength_le 𝕜 L h]
        infer_instance
      WeightedBasis.ofSubsingleton 𝕜 (lcsSub 𝕜 L k)
    else
      let bp := lcsLayerComplementBasis 𝕜 L k
      let bq :=
        WeightedBasis.map (𝕜 := 𝕜) (lcsSuccComap_equiv 𝕜 L k).symm
          (lcsWeightedBasis (k + 1))
      WeightedBasis.combine (𝕜 := 𝕜) (lcsLayerComplement_isCompl 𝕜 L k) bp bq
termination_by k => nilpotencyLength L L - k
decreasing_by
  have hk : k < nilpotencyLength L L := Nat.not_le.mp h
  omega

noncomputable def adaptedWeightedBasis : WeightedBasis 𝕜 L :=
  WeightedBasis.map (𝕜 := 𝕜) (LinearEquiv.ofTop (lcsSub 𝕜 L 0) (lcsSub_zero 𝕜 L))
    (lcsWeightedBasis 𝕜 L 0)

lemma adaptedWeightedBasis_wt_pos (i : Fin (adaptedWeightedBasis 𝕜 L).n) :
    1 ≤ (adaptedWeightedBasis 𝕜 L).wt i :=
  (adaptedWeightedBasis 𝕜 L).wt_pos i

lemma lcsWeightedBasis_wt_ge (k : ℕ)
    (i : Fin (lcsWeightedBasis 𝕜 L k).n) :
    k + 1 ≤ (lcsWeightedBasis 𝕜 L k).wt i := by
  revert i
  induction h : nilpotencyLength L L - k using Nat.strong_induction_on generalizing k with
  | h d ih =>
      intro i
      classical
      generalize hB : lcsWeightedBasis 𝕜 L k = B at i ⊢
      by_cases hk : nilpotencyLength L L ≤ k
      · haveI : Subsingleton (lcsSub 𝕜 L k) := by
          rw [lcsSub_eq_bot_of_nilpotencyLength_le 𝕜 L hk]
          infer_instance
        have hEq : lcsWeightedBasis 𝕜 L k =
            WeightedBasis.ofSubsingleton 𝕜 (lcsSub 𝕜 L k) := by
          rw [lcsWeightedBasis.eq_1]
          simp [hk]
        have hEqB : B = WeightedBasis.ofSubsingleton 𝕜 (lcsSub 𝕜 L k) :=
          hB.symm.trans hEq
        cases hEqB
        exact Fin.elim0 i
      · let bp := lcsLayerComplementBasis 𝕜 L k
        let bq :=
          WeightedBasis.map (𝕜 := 𝕜) (lcsSuccComap_equiv 𝕜 L k).symm
            (lcsWeightedBasis 𝕜 L (k + 1))
        have hEq : lcsWeightedBasis 𝕜 L k =
            WeightedBasis.combine (𝕜 := 𝕜)
              (lcsLayerComplement_isCompl 𝕜 L k) bp bq := by
          rw [lcsWeightedBasis.eq_1]
          simp [hk, bp, bq]
        have hEqB : B = WeightedBasis.combine (𝕜 := 𝕜)
              (lcsLayerComplement_isCompl 𝕜 L k) bp bq :=
          hB.symm.trans hEq
        cases hEqB
        cases hsum : finSumFinEquiv.symm i with
        | inl a =>
            have hi : i = finSumFinEquiv (Sum.inl a) := by
              simpa [hsum] using (finSumFinEquiv.apply_symm_apply i).symm
            rw [hi]
            simp [WeightedBasis.combine, bp, lcsLayerComplementBasis]
        | inr a =>
            have hi : i = finSumFinEquiv (Sum.inr a) := by
              simpa [hsum] using (finSumFinEquiv.apply_symm_apply i).symm
            rw [hi]
            simp [WeightedBasis.combine, bq, WeightedBasis.map]
            have hnext := ih (nilpotencyLength L L - (k + 1)) (by omega)
              (k + 1) (by omega) a
            omega

lemma lcsWeightedBasis_basis_mem_lcs (k : ℕ)
    (i : Fin (lcsWeightedBasis 𝕜 L k).n) :
    ((lcsWeightedBasis 𝕜 L k).basis i : L) ∈
      lcsSub 𝕜 L ((lcsWeightedBasis 𝕜 L k).wt i - 1) := by
  revert i
  induction h : nilpotencyLength L L - k using Nat.strong_induction_on generalizing k with
  | h d ih =>
      intro i
      classical
      generalize hB : lcsWeightedBasis 𝕜 L k = B at i ⊢
      by_cases hk : nilpotencyLength L L ≤ k
      · haveI : Subsingleton (lcsSub 𝕜 L k) := by
          rw [lcsSub_eq_bot_of_nilpotencyLength_le 𝕜 L hk]
          infer_instance
        have hEq : lcsWeightedBasis 𝕜 L k =
            WeightedBasis.ofSubsingleton 𝕜 (lcsSub 𝕜 L k) := by
          rw [lcsWeightedBasis.eq_1]
          simp [hk]
        have hEqB : B = WeightedBasis.ofSubsingleton 𝕜 (lcsSub 𝕜 L k) :=
          hB.symm.trans hEq
        cases hEqB
        exact Fin.elim0 i
      · let bp := lcsLayerComplementBasis 𝕜 L k
        let bq :=
          WeightedBasis.map (𝕜 := 𝕜) (lcsSuccComap_equiv 𝕜 L k).symm
            (lcsWeightedBasis 𝕜 L (k + 1))
        have hEq : lcsWeightedBasis 𝕜 L k =
            WeightedBasis.combine (𝕜 := 𝕜)
              (lcsLayerComplement_isCompl 𝕜 L k) bp bq := by
          rw [lcsWeightedBasis.eq_1]
          simp [hk, bp, bq]
        have hEqB : B = WeightedBasis.combine (𝕜 := 𝕜)
              (lcsLayerComplement_isCompl 𝕜 L k) bp bq :=
          hB.symm.trans hEq
        cases hEqB
        cases hsum : finSumFinEquiv.symm i with
        | inl a =>
            have hi : i = finSumFinEquiv (Sum.inl a) := by
              simpa [hsum] using (finSumFinEquiv.apply_symm_apply i).symm
            rw [hi]
            simp [WeightedBasis.combine, bp, lcsLayerComplementBasis]
        | inr a =>
            have hi : i = finSumFinEquiv (Sum.inr a) := by
              simpa [hsum] using (finSumFinEquiv.apply_symm_apply i).symm
            rw [hi]
            simp [WeightedBasis.combine, bq, WeightedBasis.map]
            exact ih (nilpotencyLength L L - (k + 1)) (by omega)
              (k + 1) (by omega) a

lemma adaptedWeightedBasis_basis_mem_lcs
    (i : Fin (adaptedWeightedBasis 𝕜 L).n) :
    (adaptedWeightedBasis 𝕜 L).basis i ∈
      lcsSub 𝕜 L ((adaptedWeightedBasis 𝕜 L).wt i - 1) := by
  simpa [adaptedWeightedBasis, WeightedBasis.map, Module.Basis.map_apply] using
    (lcsWeightedBasis_basis_mem_lcs (𝕜 := 𝕜) (L := L) 0 i)

noncomputable def lcsHighSpan (r k : ℕ) :
    Submodule 𝕜 (lcsSub 𝕜 L r) :=
  Submodule.span 𝕜
    ((lcsWeightedBasis 𝕜 L r).basis ''
      {i | k < (lcsWeightedBasis 𝕜 L r).wt i})

lemma lcsHighSpan_mem_of_lcs {r k : ℕ} (hrk : r ≤ k)
    {x : lcsSub 𝕜 L r} (hx : (x : L) ∈ lcsSub 𝕜 L k) :
    x ∈ lcsHighSpan 𝕜 L r k := by
  induction d : k - r using Nat.strong_induction_on generalizing r k with
  | h d ih =>
      by_cases hek : r = k
      · subst k
        rw [lcsHighSpan]
        rw [← (lcsWeightedBasis 𝕜 L r).basis.sum_repr x]
        refine sum_mem fun i _ =>
          (lcsHighSpan 𝕜 L r r).smul_mem _ ?_
        apply Submodule.subset_span
        refine ⟨i, ?_, rfl⟩
        change r < (lcsWeightedBasis 𝕜 L r).wt i
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self r)
          (lcsWeightedBasis_wt_ge 𝕜 L r i)
      · have hlt : r < k := Nat.lt_of_le_of_ne hrk hek
        have hxnext : (x : L) ∈ lcsSub 𝕜 L (r + 1) :=
          (lcsSub_mono 𝕜 L (by omega)) hx
        let e := lcsSuccComap_equiv 𝕜 L r
        let xq : lcsSuccComap 𝕜 L r := ⟨x, hxnext⟩
        let y : lcsSub 𝕜 L (r + 1) := e xq
        have hy : (y : L) ∈ lcsSub 𝕜 L k := by
          change (x : L) ∈ lcsSub 𝕜 L k
          exact hx
        have hspan : y ∈ lcsHighSpan 𝕜 L (r + 1) k := by
          apply ih (k - (r + 1)) (by omega) (hrk := by omega) hy (by omega)
        have hmap : ∀ {z : lcsSub 𝕜 L (r + 1)},
            z ∈ lcsHighSpan 𝕜 L (r + 1) k →
              ((e.symm z : lcsSuccComap 𝕜 L r) : lcsSub 𝕜 L r) ∈
                lcsHighSpan 𝕜 L r k := by
          intro z hz
          by_cases hk : nilpotencyLength L L ≤ r
          · haveI : Subsingleton (lcsSub 𝕜 L r) := by
              rw [lcsSub_eq_bot_of_nilpotencyLength_le 𝕜 L hk]
              infer_instance
            have hz0 :
                ((e.symm z : lcsSuccComap 𝕜 L r) : lcsSub 𝕜 L r) = 0 :=
              Subsingleton.elim _ _
            rw [hz0]
            exact (lcsHighSpan 𝕜 L r k).zero_mem
          · let bp := lcsLayerComplementBasis 𝕜 L r
            let bq :=
              WeightedBasis.map (𝕜 := 𝕜) (lcsSuccComap_equiv 𝕜 L r).symm
                (lcsWeightedBasis 𝕜 L (r + 1))
            have hEqr : lcsWeightedBasis 𝕜 L r =
                WeightedBasis.combine (𝕜 := 𝕜)
                  (lcsLayerComplement_isCompl 𝕜 L r) bp bq := by
              rw [lcsWeightedBasis.eq_1]
              simp [hk, bp, bq]
            rw [lcsHighSpan, hEqr]
            induction hz using Submodule.span_induction with
            | mem z hz =>
                obtain ⟨a, ha, rfl⟩ := hz
                apply Submodule.subset_span
                refine ⟨finSumFinEquiv (m := bp.n) (n := bq.n) (Sum.inr a), ?_, ?_⟩
                · change k <
                    (WeightedBasis.combine (𝕜 := 𝕜)
                      (lcsLayerComplement_isCompl 𝕜 L r) bp bq).wt
                      (finSumFinEquiv (Sum.inr a))
                  simpa [WeightedBasis.combine, bq, WeightedBasis.map] using ha
                · simp [bq, e, WeightedBasis.combine, WeightedBasis.map,
                    Module.Basis.map_apply, Module.Basis.prod_apply,
                    Module.Basis.reindex_apply,
                    Submodule.comapSubtypeEquivOfLe]
            | zero => simp
            | add u v _ _ hu hv => exact add_mem hu hv
            | smul c u _ hu => exact Submodule.smul_mem _ c hu
        have := hmap hspan
        simpa [y, xq, e, Submodule.comapSubtypeEquivOfLe] using this

noncomputable def adaptedHighSpan (k : ℕ) : Submodule 𝕜 L :=
  Submodule.span 𝕜
    ((adaptedWeightedBasis 𝕜 L).basis ''
      {i | k < (adaptedWeightedBasis 𝕜 L).wt i})

lemma lcsSub_le_adaptedHighSpan (k : ℕ) :
    lcsSub 𝕜 L k ≤ adaptedHighSpan 𝕜 L k := by
  intro x hx
  let x0 : lcsSub 𝕜 L 0 := ⟨x, by simp [lcsSub_zero 𝕜 L]⟩
  have hx0 : (x0 : L) ∈ lcsSub 𝕜 L k := by
    exact hx
  have hhigh : x0 ∈ lcsHighSpan 𝕜 L 0 k :=
    lcsHighSpan_mem_of_lcs 𝕜 L (Nat.zero_le _) hx0
  rw [lcsHighSpan] at hhigh
  change (x0 : L) ∈ adaptedHighSpan 𝕜 L k
  refine Submodule.span_induction
    (p := fun (z : lcsSub 𝕜 L 0) _ => (z : L) ∈ adaptedHighSpan 𝕜 L k)
    ?_ ?_ ?_ ?_ hhigh
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨i, ?_, ?_⟩
    · simpa [adaptedHighSpan, adaptedWeightedBasis, WeightedBasis.map] using hi
    · rfl
  · simp [adaptedHighSpan]
  · intro u v _ _ hu hv
    exact add_mem hu hv
  · intro c u _ hu
    exact (adaptedHighSpan 𝕜 L k).smul_mem c hu

lemma adapted_repr_support_of_lcs {k : ℕ} {x : L}
    (hx : x ∈ lcsSub 𝕜 L k) (i : Fin (adaptedWeightedBasis 𝕜 L).n)
    (hi : (adaptedWeightedBasis 𝕜 L).basis.repr x i ≠ 0) :
    k < (adaptedWeightedBasis 𝕜 L).wt i := by
  have hmem : x ∈ adaptedHighSpan 𝕜 L k :=
    lcsSub_le_adaptedHighSpan 𝕜 L k hx
  have hsupp :
      ((↑((adaptedWeightedBasis 𝕜 L).basis.repr x).support :
          Set (Fin (adaptedWeightedBasis 𝕜 L).n))) ⊆
        {i | k < (adaptedWeightedBasis 𝕜 L).wt i} := by
    exact Module.Basis.repr_support_subset_of_mem_span
      (adaptedWeightedBasis 𝕜 L).basis _ hmem
  exact hsupp (Finsupp.mem_support_iff.mpr hi)

lemma adapted_bracket_repr_support
    (i j k : Fin (adaptedWeightedBasis 𝕜 L).n)
    (hcoef : (adaptedWeightedBasis 𝕜 L).basis.repr
        ⁅(adaptedWeightedBasis 𝕜 L).basis i,
          (adaptedWeightedBasis 𝕜 L).basis j⁆ k ≠ 0) :
    (adaptedWeightedBasis 𝕜 L).wt i +
        (adaptedWeightedBasis 𝕜 L).wt j ≤
      (adaptedWeightedBasis 𝕜 L).wt k := by
  have hbr := lie_mem_lcs_add 𝕜 L
    (a := (adaptedWeightedBasis 𝕜 L).wt i - 1)
    (b := (adaptedWeightedBasis 𝕜 L).wt j - 1)
    (x := (adaptedWeightedBasis 𝕜 L).basis i)
    (y := (adaptedWeightedBasis 𝕜 L).basis j)
    (adaptedWeightedBasis_basis_mem_lcs 𝕜 L i)
    (adaptedWeightedBasis_basis_mem_lcs 𝕜 L j)
  have hs := adapted_repr_support_of_lcs 𝕜 L hbr k hcoef
  omega

/-! ### Words and the high-weight ideal -/

noncomputable def adaptedCutoff : ℕ :=
  (Finset.univ.sup (adaptedWeightedBasis 𝕜 L).wt) + 1

lemma adaptedCutoff_gt_weight (i : Fin (adaptedWeightedBasis 𝕜 L).n) :
    (adaptedWeightedBasis 𝕜 L).wt i < adaptedCutoff 𝕜 L :=
  Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))

noncomputable def adaptedWordWeight {k : ℕ}
    (f : Fin k → Fin (adaptedWeightedBasis 𝕜 L).n) : ℕ :=
  ∑ i, (adaptedWeightedBasis 𝕜 L).wt (f i)

noncomputable def adaptedIotaWord {k : ℕ}
    (f : Fin k → Fin (adaptedWeightedBasis 𝕜 L).n) : U :=
  iotaWord 𝕜 L (List.ofFn fun i => (adaptedWeightedBasis 𝕜 L).basis (f i))

lemma adaptedWordWeight_ge_length {k : ℕ}
    (f : Fin k → Fin (adaptedWeightedBasis 𝕜 L).n) :
    k ≤ adaptedWordWeight 𝕜 L f := by
  have h : ∑ _i : Fin k, (1 : ℕ) ≤ adaptedWordWeight 𝕜 L f :=
    Finset.sum_le_sum fun i _ => adaptedWeightedBasis_wt_pos 𝕜 L (f i)
  simpa [Fin.sum_univ_eq_sum_range] using h

lemma adaptedWordWeight_snoc {k : ℕ}
    (f : Fin k → Fin (adaptedWeightedBasis 𝕜 L).n)
    (i : Fin (adaptedWeightedBasis 𝕜 L).n) :
    adaptedWordWeight 𝕜 L (Fin.snoc f i) =
      adaptedWordWeight 𝕜 L f + (adaptedWeightedBasis 𝕜 L).wt i := by
  simp [adaptedWordWeight, Fin.sum_univ_castSucc]

noncomputable def nilpotentWeightedLeftIdeal (N : ℕ) : Submodule U U :=
  Submodule.span U
    {u | ∃ (a b : U) (k : ℕ)
      (f : Fin k → Fin (adaptedWeightedBasis 𝕜 L).n),
      N ≤ adaptedWordWeight 𝕜 L f ∧
        u = a * adaptedIotaWord 𝕜 L f * b}

lemma nilpotentWeightedLeftIdeal_left_stable {N : ℕ} {a u : U}
    (hu : u ∈ nilpotentWeightedLeftIdeal 𝕜 L N) :
    a * u ∈ nilpotentWeightedLeftIdeal 𝕜 L N := by
  exact Submodule.smul_mem _ a hu

lemma nilpotentWeightedLeftIdeal_right_stable {N : ℕ} {u v : U}
    (hu : u ∈ nilpotentWeightedLeftIdeal 𝕜 L N) :
    u * v ∈ nilpotentWeightedLeftIdeal 𝕜 L N := by
  refine Submodule.span_induction
    (p := fun u _ => u * v ∈ nilpotentWeightedLeftIdeal 𝕜 L N)
    ?_ ?_ ?_ ?_ hu
  · rintro u ⟨a, b, k, f, hw, rfl⟩
    apply Submodule.subset_span
    refine ⟨a, b * v, k, f, hw, ?_⟩
    simp [mul_assoc]
  · simp
  · intro a b _ _ ha hb
    rw [add_mul]
    exact add_mem ha hb
  · intro r a _ ha
    simpa only [smul_mul_assoc] using (Submodule.smul_mem _ r ha)

lemma nilpotentWeightedLeftIdeal_derivation_stable {N : ℕ} (h : L) {u : U}
    (hu : u ∈ nilpotentWeightedLeftIdeal 𝕜 L N) :
    UniversalEnvelopingAlgebra.ι 𝕜 h * u -
        u * UniversalEnvelopingAlgebra.ι 𝕜 h ∈
      nilpotentWeightedLeftIdeal 𝕜 L N := by
  exact sub_mem (nilpotentWeightedLeftIdeal_left_stable 𝕜 L hu)
    (nilpotentWeightedLeftIdeal_right_stable 𝕜 L hu)

lemma envelopingLengthLeftIdeal_le_nilpotentWeightedLeftIdeal {n : ℕ}
    (hn : adaptedCutoff 𝕜 L ≤ n) :
    envelopingLengthLeftIdeal 𝕜 L n ≤
      nilpotentWeightedLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L) := by
  refine Submodule.span_le.2 ?_
  rintro u ⟨xs, rfl⟩
  let b := (adaptedWeightedBasis 𝕜 L).basis
  have hexp_b :
      TensorAlgebra.tprod 𝕜 L n xs =
        ∑ f : Fin n → Fin (adaptedWeightedBasis 𝕜 L).n,
          (∏ i, b.repr (xs i) (f i)) •
            TensorAlgebra.tprod 𝕜 L n (fun i => b (f i)) := by
    let xs' : Fin n → L := fun i => ∑ j, b.repr (xs i) j • b j
    have hxs' : xs = xs' := by
      ext i
      exact (b.sum_repr (xs i)).symm
    rw [hxs']
    rw [MultilinearMap.map_sum (TensorAlgebra.tprod 𝕜 L n)
      (g := fun i j => b.repr (xs i) j • b j)]
    refine Finset.sum_congr rfl fun f _ => ?_
    simpa [xs'] using (TensorAlgebra.tprod 𝕜 L n).map_smul_univ
      (fun i => b.repr (xs i) (f i)) (fun i => b (f i))
  change iotaWord 𝕜 L (List.ofFn xs) ∈
    nilpotentWeightedLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L)
  rw [iotaWord_ofFn 𝕜 L, hexp_b, map_sum]
  refine sum_mem fun f _ => ?_
  rw [map_smul]
  have hw : adaptedCutoff 𝕜 L ≤ adaptedWordWeight 𝕜 L f :=
    hn.trans (adaptedWordWeight_ge_length 𝕜 L f)
  have hgen : adaptedIotaWord 𝕜 L f ∈
      nilpotentWeightedLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L) := by
    apply Submodule.subset_span
    exact ⟨1, 1, n, f, hw, by simp [adaptedIotaWord, iotaWord_ofFn]⟩
  rw [Algebra.smul_def]
  simpa [adaptedIotaWord, iotaWord_ofFn] using
    (Submodule.smul_mem _ (algebraMap 𝕜 U (∏ i, b.repr (xs i) (f i))) hgen)

lemma finiteDimensional_nilpotentWeightedQuotient :
    FiniteDimensional 𝕜
      (U ⧸ (nilpotentWeightedLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L)).restrictScalars 𝕜) := by
  haveI := finiteDimensional_envelopingLengthQuotient 𝕜 L (adaptedCutoff 𝕜 L)
  let p := (envelopingLengthLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L)).restrictScalars 𝕜
  let q := (nilpotentWeightedLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L)).restrictScalars 𝕜
  have hpq : p ≤ q := envelopingLengthLeftIdeal_le_nilpotentWeightedLeftIdeal 𝕜 L le_rfl
  exact FiniteDimensional.of_surjective (Submodule.factor hpq)
    (Submodule.factor_surjective hpq)

/-! ### The actual PBW interface and degree one -/

noncomputable def orderedPBWMonomial {n : ℕ}
    (b : Module.Basis (Fin n) 𝕜 L) (α : Fin n →₀ ℕ) : U :=
  TauCeti.UniversalEnvelopingAlgebra.orderedBasisMonomial b α

noncomputable def multiIndexWeight {n : ℕ} (wt : Fin n → ℕ)
    (α : Fin n →₀ ℕ) : ℕ := α.sum fun i k => k * wt i

def HasOrderedPBWBasis {n : ℕ}
    (b : Module.Basis (Fin n) 𝕜 L) : Prop :=
  LinearIndependent 𝕜 (orderedPBWMonomial 𝕜 L b)

lemma realPBW_hasOrderedPBWBasis :
    HasOrderedPBWBasis 𝕜 L (adaptedWeightedBasis 𝕜 L).basis := by
  exact TauCeti.UniversalEnvelopingAlgebra.linearIndependent_orderedBasisMonomial
    (R := 𝕜) (L := L) (adaptedWeightedBasis 𝕜 L).basis

lemma ordered_length_one_weight (i : Fin (adaptedWeightedBasis 𝕜 L).n) :
    multiIndexWeight (adaptedWeightedBasis 𝕜 L).wt (Finsupp.single i 1) =
      (adaptedWeightedBasis 𝕜 L).wt i := by
  simp [multiIndexWeight, Finsupp.sum_single_index]

lemma orderedPBWMonomial_single (i : Fin (adaptedWeightedBasis 𝕜 L).n) :
    orderedPBWMonomial 𝕜 L (adaptedWeightedBasis 𝕜 L).basis
        (Finsupp.single i 1) =
      UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis i) := by
  simp [orderedPBWMonomial,
    TauCeti.UniversalEnvelopingAlgebra.orderedBasisMonomial,
    TauCeti.UniversalEnvelopingAlgebra.multiIndexToList,
    iotaWord, Finsupp.toMultiset_single]

noncomputable def highWeightOrderedSpan (N : ℕ) : Submodule 𝕜 U :=
  Submodule.span 𝕜
    (orderedPBWMonomial 𝕜 L (adaptedWeightedBasis 𝕜 L).basis ''
      {α | N ≤ multiIndexWeight (adaptedWeightedBasis 𝕜 L).wt α})

noncomputable def adaptedListWeight
    (w : List (Fin (adaptedWeightedBasis 𝕜 L).n)) : ℕ :=
  (w.map (adaptedWeightedBasis 𝕜 L).wt).sum

noncomputable def adaptedRawWord
    (w : List (Fin (adaptedWeightedBasis 𝕜 L).n)) : U :=
  iotaWord 𝕜 L (w.map (adaptedWeightedBasis 𝕜 L).basis)

lemma adaptedListWeight_append
    (u v : List (Fin (adaptedWeightedBasis 𝕜 L).n)) :
    adaptedListWeight 𝕜 L (u ++ v) =
      adaptedListWeight 𝕜 L u + adaptedListWeight 𝕜 L v := by
  simp [adaptedListWeight]

lemma adaptedListWeight_cons
    (a : Fin (adaptedWeightedBasis 𝕜 L).n)
    (s : List (Fin (adaptedWeightedBasis 𝕜 L).n)) :
    adaptedListWeight 𝕜 L (a :: s) =
      (adaptedWeightedBasis 𝕜 L).wt a + adaptedListWeight 𝕜 L s := by
  rfl

lemma adaptedListWeight_orderedInsert
    (a : Fin (adaptedWeightedBasis 𝕜 L).n)
    (s : List (Fin (adaptedWeightedBasis 𝕜 L).n)) :
    adaptedListWeight 𝕜 L (s.orderedInsert (· ≤ ·) a) =
      adaptedListWeight 𝕜 L (a :: s) := by
  induction s with
  | nil => simp [adaptedListWeight]
  | cons b s ih =>
      by_cases hab : a ≤ b
      · rw [List.orderedInsert_cons_of_le (r := (· ≤ ·)) _ hab]
      · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) _ hab]
        change (adaptedWeightedBasis 𝕜 L).wt b +
            adaptedListWeight 𝕜 L (s.orderedInsert (· ≤ ·) a) =
          (adaptedWeightedBasis 𝕜 L).wt a +
            ((adaptedWeightedBasis 𝕜 L).wt b + adaptedListWeight 𝕜 L s)
        rw [ih]
        simp only [adaptedListWeight, List.map_cons, List.sum_cons]
        omega

lemma adaptedListWeight_insertionSort
    (s : List (Fin (adaptedWeightedBasis 𝕜 L).n)) :
    adaptedListWeight 𝕜 L (s.insertionSort (· ≤ ·)) =
      adaptedListWeight 𝕜 L s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      rw [List.insertionSort_cons, adaptedListWeight_orderedInsert]
      simpa [adaptedListWeight] using
        congrArg (fun z : ℕ => (adaptedWeightedBasis 𝕜 L).wt a + z) ih

lemma adaptedRawWord_append
    (u v : List (Fin (adaptedWeightedBasis 𝕜 L).n)) :
    adaptedRawWord 𝕜 L (u ++ v) =
      adaptedRawWord 𝕜 L u * adaptedRawWord 𝕜 L v := by
  simp [adaptedRawWord, iotaWord, List.map_append, List.prod_append]

lemma adaptedRawWord_adjacent_swap
    (p t q : List (Fin (adaptedWeightedBasis 𝕜 L).n))
    (a c : Fin (adaptedWeightedBasis 𝕜 L).n) :
    adaptedRawWord 𝕜 L (p ++ a :: c :: t ++ q) -
        adaptedRawWord 𝕜 L (p ++ c :: a :: t ++ q) =
      adaptedRawWord 𝕜 L p *
          UniversalEnvelopingAlgebra.ι 𝕜
            ⁅(adaptedWeightedBasis 𝕜 L).basis a,
              (adaptedWeightedBasis 𝕜 L).basis c⁆ *
        adaptedRawWord 𝕜 L (t ++ q) := by
  have hrel :
      UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis a) *
          UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis c) -
        UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis c) *
          UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis a) =
        UniversalEnvelopingAlgebra.ι 𝕜
          ⁅(adaptedWeightedBasis 𝕜 L).basis a,
            (adaptedWeightedBasis 𝕜 L).basis c⁆ := by
    have hlie := LieHom.map_lie
      (UniversalEnvelopingAlgebra.ι 𝕜 (L := L))
      ((adaptedWeightedBasis 𝕜 L).basis a)
      ((adaptedWeightedBasis 𝕜 L).basis c)
    simpa [LieRing.of_associative_ring_bracket] using hlie.symm
  rw [show adaptedRawWord 𝕜 L (p ++ a :: c :: t ++ q) =
      adaptedRawWord 𝕜 L p *
        (UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis a) *
          UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis c)) *
        adaptedRawWord 𝕜 L (t ++ q) by
      simp [adaptedRawWord, iotaWord, List.map_append, List.prod_append,
        List.map_cons, List.prod_cons, mul_assoc]]
  rw [show adaptedRawWord 𝕜 L (p ++ c :: a :: t ++ q) =
      adaptedRawWord 𝕜 L p *
        (UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis c) *
          UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis a)) *
        adaptedRawWord 𝕜 L (t ++ q) by
      simp [adaptedRawWord, iotaWord, List.map_append, List.prod_append,
        List.map_cons, List.prod_cons, mul_assoc]]
  calc
    adaptedRawWord 𝕜 L p *
          (UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis a) *
            UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis c)) *
        adaptedRawWord 𝕜 L (t ++ q) -
      adaptedRawWord 𝕜 L p *
          (UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis c) *
            UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis a)) *
        adaptedRawWord 𝕜 L (t ++ q) =
      adaptedRawWord 𝕜 L p *
          (UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis a) *
            UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis c) -
              UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis c) *
                UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis a)) *
        adaptedRawWord 𝕜 L (t ++ q) := by
          rw [mul_sub, sub_mul]
    _ = _ := by rw [hrel]

lemma adapted_iota_repr_sum
    (x : L) :
    UniversalEnvelopingAlgebra.ι 𝕜 x =
      ∑ i, (adaptedWeightedBasis 𝕜 L).basis.repr x i •
        UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis i) := by
  calc
    UniversalEnvelopingAlgebra.ι 𝕜 x =
        UniversalEnvelopingAlgebra.ι 𝕜
          (∑ i, (adaptedWeightedBasis 𝕜 L).basis.repr x i •
            (adaptedWeightedBasis 𝕜 L).basis i) := by
      rw [(adaptedWeightedBasis 𝕜 L).basis.sum_repr]
    _ = ∑ i, (adaptedWeightedBasis 𝕜 L).basis.repr x i •
        UniversalEnvelopingAlgebra.ι 𝕜 ((adaptedWeightedBasis 𝕜 L).basis i) := by
      change (UniversalEnvelopingAlgebra.mkAlgHom 𝕜 L)
          ((TensorAlgebra.ι 𝕜) (∑ i, (adaptedWeightedBasis 𝕜 L).basis.repr x i •
            (adaptedWeightedBasis 𝕜 L).basis i)) = _
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [map_smul]
      rfl

lemma adapted_multiIndexToList_toFinsupp
    (s : List (Fin (adaptedWeightedBasis 𝕜 L).n))
    (hs : s.Pairwise (· ≤ ·)) :
    TauCeti.UniversalEnvelopingAlgebra.multiIndexToList
        (Multiset.toFinsupp (s : Multiset (Fin (adaptedWeightedBasis 𝕜 L).n))) = s := by
  simp [TauCeti.UniversalEnvelopingAlgebra.multiIndexToList,
    Multiset.toFinsupp_toMultiset, Multiset.coe_sort]
  exact List.mergeSort_eq_self (· ≤ ·) hs

lemma adapted_multiIndexWeight_toFinsupp
    (s : List (Fin (adaptedWeightedBasis 𝕜 L).n)) :
    multiIndexWeight (adaptedWeightedBasis 𝕜 L).wt
        (Multiset.toFinsupp (s : Multiset (Fin (adaptedWeightedBasis 𝕜 L).n))) =
      adaptedListWeight 𝕜 L s := by
  classical
  change (Multiset.toFinsupp (s : Multiset (Fin (adaptedWeightedBasis 𝕜 L).n))).sum
      (fun i k => k * (adaptedWeightedBasis 𝕜 L).wt i) =
    (s.map (adaptedWeightedBasis 𝕜 L).wt).sum
  simp only [Finsupp.sum, Multiset.toFinsupp_support,
    Multiset.toFinsupp_apply]
  simpa [nsmul_eq_mul] using
    (Finset.sum_multiset_map_count
      (s : Multiset (Fin (adaptedWeightedBasis 𝕜 L).n))
      (adaptedWeightedBasis 𝕜 L).wt).symm

lemma adaptedRawWord_eq_orderedPBWMonomial_of_pairwise
    (s : List (Fin (adaptedWeightedBasis 𝕜 L).n))
    (hs : s.Pairwise (· ≤ ·)) :
    adaptedRawWord 𝕜 L s =
      orderedPBWMonomial 𝕜 L (adaptedWeightedBasis 𝕜 L).basis
        (Multiset.toFinsupp (s : Multiset (Fin (adaptedWeightedBasis 𝕜 L).n))) := by
  simp [adaptedRawWord, orderedPBWMonomial,
    TauCeti.UniversalEnvelopingAlgebra.orderedBasisMonomial,
    TauCeti.UniversalEnvelopingAlgebra.pbwMonomial_def,
    iotaWord, Function.comp_def,
    adapted_multiIndexToList_toFinsupp 𝕜 L s hs]

lemma adaptedRawWord_mem_highWeightOrderedSpan_of_pairwise
    (s : List (Fin (adaptedWeightedBasis 𝕜 L).n))
    (hs : s.Pairwise (· ≤ ·))
    (hN : adaptedCutoff 𝕜 L ≤ adaptedListWeight 𝕜 L s) :
    adaptedRawWord 𝕜 L s ∈ highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
  apply Submodule.subset_span
  refine ⟨Multiset.toFinsupp (s : Multiset (Fin (adaptedWeightedBasis 𝕜 L).n)), ?_, ?_⟩
  · simpa [adapted_multiIndexWeight_toFinsupp 𝕜 L s] using hN
  · exact (adaptedRawWord_eq_orderedPBWMonomial_of_pairwise 𝕜 L s hs).symm

lemma adaptedRawWord_mem_highWeightOrderedSpan
    (s : List (Fin (adaptedWeightedBasis 𝕜 L).n))
    (hN : adaptedCutoff 𝕜 L ≤ adaptedListWeight 𝕜 L s) :
    adaptedRawWord 𝕜 L s ∈ highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
  revert hN
  induction hlen : s.length using Nat.strong_induction_on generalizing s with
  | h n ih =>
      intro hN
      have insertDefect :
          ∀ (p : List (Fin (adaptedWeightedBasis 𝕜 L).n))
            (a : Fin (adaptedWeightedBasis 𝕜 L).n)
            (t : List (Fin (adaptedWeightedBasis 𝕜 L).n))
            (q : List (Fin (adaptedWeightedBasis 𝕜 L).n)),
            t.Pairwise (· ≤ ·) →
            (p ++ a :: t ++ q).length = n →
            adaptedCutoff 𝕜 L ≤ adaptedListWeight 𝕜 L (p ++ a :: t ++ q) →
            adaptedRawWord 𝕜 L (p ++ a :: t ++ q) -
                adaptedRawWord 𝕜 L (p ++
                  t.orderedInsert (· ≤ ·) a ++ q) ∈
              highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
        intro p a t q
        induction t generalizing p with
        | nil =>
            intro hs hlen hweight
            simp [adaptedRawWord]
        | cons b t ihinsert =>
            intro hs hlen hweight
            cases hs with
            | cons hab htail =>
                by_cases ha : a ≤ b
                · rw [List.orderedInsert_cons_of_le (r := (· ≤ ·)) _ ha]
                  simp [adaptedRawWord]
                · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) _ ha]
                  have hi := ihinsert (p := p ++ [b]) htail
                    (by simpa [List.length_append] using hlen)
                    (by
                      simpa [adaptedListWeight, List.append_assoc,
                        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hweight)
                  have hbr :
                      adaptedRawWord 𝕜 L p *
                          UniversalEnvelopingAlgebra.ι 𝕜
                            ⁅(adaptedWeightedBasis 𝕜 L).basis a,
                              (adaptedWeightedBasis 𝕜 L).basis b⁆ *
                        adaptedRawWord 𝕜 L (t ++ q) ∈
                        highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
                    rw [adapted_iota_repr_sum]
                    rw [Finset.mul_sum, Finset.sum_mul]
                    refine sum_mem fun k _ => ?_
                    by_cases hk :
                        (adaptedWeightedBasis 𝕜 L).basis.repr
                            ⁅(adaptedWeightedBasis 𝕜 L).basis a,
                              (adaptedWeightedBasis 𝕜 L).basis b⁆ k = 0
                    · simp [hk]
                    · have hwtcoef := adapted_bracket_repr_support 𝕜 L a b k hk
                      have hshort : (p ++ [k] ++ t ++ q).length < n := by
                        simp [List.length_append] at hlen ⊢
                        omega
                      have hweightk :
                          adaptedCutoff 𝕜 L ≤
                            adaptedListWeight 𝕜 L (p ++ [k] ++ t ++ q) := by
                        simp [adaptedListWeight, List.append_assoc] at hweight ⊢
                        omega
                      have hraw : adaptedRawWord 𝕜 L (p ++ [k] ++ t ++ q) ∈
                          highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
                        exact ih _ hshort _ rfl hweightk
                      have hterm :
                          adaptedRawWord 𝕜 L p *
                              ((adaptedWeightedBasis 𝕜 L).basis.repr
                                  ⁅(adaptedWeightedBasis 𝕜 L).basis a,
                                    (adaptedWeightedBasis 𝕜 L).basis b⁆ k •
                                UniversalEnvelopingAlgebra.ι 𝕜
                                  ((adaptedWeightedBasis 𝕜 L).basis k)) *
                            adaptedRawWord 𝕜 L (t ++ q) =
                          (adaptedWeightedBasis 𝕜 L).basis.repr
                              ⁅(adaptedWeightedBasis 𝕜 L).basis a,
                                (adaptedWeightedBasis 𝕜 L).basis b⁆ k •
                            adaptedRawWord 𝕜 L (p ++ [k] ++ t ++ q) := by
                        calc
                          _ = algebraMap 𝕜 U
                                ((adaptedWeightedBasis 𝕜 L).basis.repr
                                  ⁅(adaptedWeightedBasis 𝕜 L).basis a,
                                    (adaptedWeightedBasis 𝕜 L).basis b⁆ k) *
                                (adaptedRawWord 𝕜 L p *
                                  UniversalEnvelopingAlgebra.ι 𝕜
                                    ((adaptedWeightedBasis 𝕜 L).basis k) *
                                  adaptedRawWord 𝕜 L (t ++ q)) := by
                            rw [Algebra.smul_def]
                            rw [← mul_assoc]
                            rw [← Algebra.commutes]
                            simp only [mul_assoc]
                          _ = _ := by
                            rw [Algebra.smul_def]
                            simp [adaptedRawWord, iotaWord,
                              List.map_append, List.map_cons, List.prod_append,
                              List.prod_cons, Function.comp_def, mul_assoc]
                      rw [hterm]
                      exact (highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L)).smul_mem _ hraw
                  have hfirst :
                      adaptedRawWord 𝕜 L (p ++ a :: b :: t ++ q) -
                          adaptedRawWord 𝕜 L (p ++ b :: a :: t ++ q) ∈
                        highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
                    rw [adaptedRawWord_adjacent_swap]
                    exact hbr
                  rw [← sub_add_sub_cancel
                    (adaptedRawWord 𝕜 L (p ++ a :: b :: t ++ q))
                    (adaptedRawWord 𝕜 L (p ++ b :: a :: t ++ q))
                    (adaptedRawWord 𝕜 L (p ++ b :: t.orderedInsert (· ≤ ·) a ++ q))]
                  have hi' :
                      adaptedRawWord 𝕜 L (p ++ b :: a :: t ++ q) -
                          adaptedRawWord 𝕜 L (p ++ b :: t.orderedInsert (· ≤ ·) a ++ q) ∈
                        highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
                    simpa [List.singleton_append, List.append_assoc] using hi
                  exact add_mem hfirst hi'
      have hdefect :
          ∀ (p : List (Fin (adaptedWeightedBasis 𝕜 L).n))
            (t : List (Fin (adaptedWeightedBasis 𝕜 L).n))
            (q : List (Fin (adaptedWeightedBasis 𝕜 L).n)),
            (p ++ t ++ q).length = n →
            adaptedCutoff 𝕜 L ≤ adaptedListWeight 𝕜 L (p ++ t ++ q) →
            adaptedRawWord 𝕜 L (p ++ t ++ q) -
                adaptedRawWord 𝕜 L (p ++ t.insertionSort (· ≤ ·) ++ q) ∈
              highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
        intro p t q hlen hweight
        induction t generalizing p with
        | nil => simp [adaptedRawWord]
        | cons a t ih =>
            rw [List.insertionSort_cons]
            have hleft := ih (p := p ++ [a])
              (by simpa [List.length_append] using hlen)
              (by simpa [adaptedListWeight, List.append_assoc,
                Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hweight)
            have hright := insertDefect p a (t.insertionSort (· ≤ ·)) q
              (List.pairwise_insertionSort (· ≤ ·) t)
              (by simpa [List.length_append] using hlen)
              (by
                have hsortwt :
                    adaptedListWeight 𝕜 L (p ++ a :: t.insertionSort (· ≤ ·) ++ q) =
                      adaptedListWeight 𝕜 L (p ++ a :: t ++ q) := by
                  simp only [adaptedListWeight_append, adaptedListWeight_cons,
                    adaptedListWeight_insertionSort 𝕜 L t]
                rw [hsortwt]
                exact hweight)
            have hsum :
                adaptedRawWord 𝕜 L (p ++ a :: t ++ q) -
                    adaptedRawWord 𝕜 L
                      (p ++ List.orderedInsert (· ≤ ·) a (t.insertionSort (· ≤ ·)) ++ q) =
                  (adaptedRawWord 𝕜 L (p ++ a :: t ++ q) -
                    adaptedRawWord 𝕜 L (p ++ a :: t.insertionSort (· ≤ ·) ++ q)) +
                    (adaptedRawWord 𝕜 L (p ++ a :: t.insertionSort (· ≤ ·) ++ q) -
                      adaptedRawWord 𝕜 L
                        (p ++ List.orderedInsert (· ≤ ·) a (t.insertionSort (· ≤ ·)) ++ q)) := by
              abel
            rw [hsum]
            have hleft' :
                adaptedRawWord 𝕜 L (p ++ a :: t ++ q) -
                    adaptedRawWord 𝕜 L (p ++ a :: t.insertionSort (· ≤ ·) ++ q) ∈
                  highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
              simpa [List.singleton_append, List.append_assoc] using hleft
            exact add_mem hleft' hright
      have hdef := hdefect [] s [] (by simpa using hlen) (by simpa using hN)
      have hsorted := adaptedRawWord_mem_highWeightOrderedSpan_of_pairwise 𝕜 L
        (s.insertionSort (· ≤ ·))
        (List.pairwise_insertionSort (· ≤ ·) s)
        (by simpa [adaptedListWeight_insertionSort 𝕜 L s] using hN)
      have hadd := add_mem hdef hsorted
      simpa [adaptedRawWord] using hadd

lemma adapted_toFinsupp_multiIndexToList
    (α : Fin (adaptedWeightedBasis 𝕜 L).n →₀ ℕ) :
    Multiset.toFinsupp
        (TauCeti.UniversalEnvelopingAlgebra.multiIndexToList α :
          Multiset (Fin (adaptedWeightedBasis 𝕜 L).n)) = α := by
  simp [TauCeti.UniversalEnvelopingAlgebra.multiIndexToList,
    Multiset.sort_eq, Finsupp.toMultiset_toFinsupp]

lemma adaptedListWeight_multiIndexToList
    (α : Fin (adaptedWeightedBasis 𝕜 L).n →₀ ℕ) :
    adaptedListWeight 𝕜 L
        (TauCeti.UniversalEnvelopingAlgebra.multiIndexToList α) =
      multiIndexWeight (adaptedWeightedBasis 𝕜 L).wt α := by
  have h := adapted_multiIndexWeight_toFinsupp 𝕜 L
    (TauCeti.UniversalEnvelopingAlgebra.multiIndexToList α)
  rw [adapted_toFinsupp_multiIndexToList 𝕜 L α] at h
  exact h.symm

lemma adaptedOrderedPBWBasis_context_mem_highWeight
    (a b : U)
    (w : List (Fin (adaptedWeightedBasis 𝕜 L).n))
    (hN : adaptedCutoff 𝕜 L ≤ adaptedListWeight 𝕜 L w) :
    a * adaptedRawWord 𝕜 L w * b ∈
      highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
  let B := TauCeti.UniversalEnvelopingAlgebra.orderedPBWBasis
    (adaptedWeightedBasis 𝕜 L).basis
  have hmonomial : ∀ α β : Fin (adaptedWeightedBasis 𝕜 L).n →₀ ℕ,
      B α * adaptedRawWord 𝕜 L w * B β ∈
        highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
    intro α β
    let sa := TauCeti.UniversalEnvelopingAlgebra.multiIndexToList α
    let sb := TauCeti.UniversalEnvelopingAlgebra.multiIndexToList β
    have hα : B α = adaptedRawWord 𝕜 L sa := by
      simp [B, sa, adaptedRawWord, iotaWord,
        TauCeti.UniversalEnvelopingAlgebra.orderedPBWBasis_apply,
        TauCeti.UniversalEnvelopingAlgebra.orderedBasisMonomial,
        TauCeti.UniversalEnvelopingAlgebra.pbwMonomial_def, Function.comp_def]
    have hβ : B β = adaptedRawWord 𝕜 L sb := by
      simp [B, sb, adaptedRawWord, iotaWord,
        TauCeti.UniversalEnvelopingAlgebra.orderedPBWBasis_apply,
        TauCeti.UniversalEnvelopingAlgebra.orderedBasisMonomial,
        TauCeti.UniversalEnvelopingAlgebra.pbwMonomial_def, Function.comp_def]
    have hweight : adaptedCutoff 𝕜 L ≤
        adaptedListWeight 𝕜 L (sa ++ w ++ sb) := by
      rw [adaptedListWeight_append, adaptedListWeight_append,
        adaptedListWeight_multiIndexToList 𝕜 L α,
        adaptedListWeight_multiIndexToList 𝕜 L β]
      omega
    have hraw := adaptedRawWord_mem_highWeightOrderedSpan 𝕜 L
      (sa ++ w ++ sb) hweight
    simpa [hα, hβ, adaptedRawWord_append, List.append_assoc, mul_assoc] using hraw
  have hrepr_a : a =
      ∑ α ∈ (B.repr a).support, (B.repr a α) • B α := by
    calc
      a = Finsupp.linearCombination 𝕜 B (B.repr a) :=
        (B.linearCombination_repr a).symm
      _ = ∑ α ∈ (B.repr a).support, (B.repr a α) • B α := by
        simp [Finsupp.linearCombination_apply, Finsupp.sum]
  have hrepr_b : b =
      ∑ β ∈ (B.repr b).support, (B.repr b β) • B β := by
    calc
      b = Finsupp.linearCombination 𝕜 B (B.repr b) :=
        (B.linearCombination_repr b).symm
      _ = ∑ β ∈ (B.repr b).support, (B.repr b β) • B β := by
        simp [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hrepr_a, hrepr_b]
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  refine (highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L)).sum_mem fun β _ => ?_
  refine (highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L)).sum_mem fun α _ => ?_
  simpa [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, mul_comm] using
    (highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L)).smul_mem
      ((B.repr a α) * (B.repr b β)) (hmonomial α β)

lemma iota_not_mem_highWeightOrderedSpan_of_PBW
    (hPBW : HasOrderedPBWBasis 𝕜 L (adaptedWeightedBasis 𝕜 L).basis)
    {x : L} (hx : x ≠ 0) :
    UniversalEnvelopingAlgebra.ι 𝕜 x ∉
      highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
  let b := (adaptedWeightedBasis 𝕜 L).basis
  let wt := (adaptedWeightedBasis 𝕜 L).wt
  let v := orderedPBWMonomial 𝕜 L b
  let S : Set (Fin (adaptedWeightedBasis 𝕜 L).n →₀ ℕ) :=
    {α | adaptedCutoff 𝕜 L ≤ multiIndexWeight wt α}
  have hli : LinearIndependent 𝕜 v := hPBW
  have hxexp : UniversalEnvelopingAlgebra.ι 𝕜 x =
      ∑ i, b.repr x i • UniversalEnvelopingAlgebra.ι 𝕜 (b i) := by
    calc
      UniversalEnvelopingAlgebra.ι 𝕜 x =
          UniversalEnvelopingAlgebra.ι 𝕜 (∑ i, b.repr x i • b i) := by
            rw [b.sum_repr]
      _ = ∑ i, b.repr x i • UniversalEnvelopingAlgebra.ι 𝕜 (b i) := by
            change (UniversalEnvelopingAlgebra.mkAlgHom 𝕜 L)
                ((TensorAlgebra.ι 𝕜) (∑ i, b.repr x i • b i)) =
              ∑ i, b.repr x i •
                (UniversalEnvelopingAlgebra.mkAlgHom 𝕜 L)
                  ((TensorAlgebra.ι 𝕜) (b i))
            rw [map_sum, map_sum]
            apply Finset.sum_congr rfl
            intro i hi
            simp only [map_smul]
  have hsupp : ∃ i, b.repr x i ≠ 0 := by
    by_contra h0
    apply hx
    have hrepr : b.repr x = 0 := by
      ext i
      by_contra hi
      exact h0 ⟨i, hi⟩
    exact b.repr.injective (by simpa using hrepr)
  obtain ⟨i, hi⟩ := hsupp
  have hnot : Finsupp.single i 1 ∉ S := by
    intro h
    change adaptedCutoff 𝕜 L ≤ multiIndexWeight wt (Finsupp.single i 1) at h
    have hweight : multiIndexWeight wt (Finsupp.single i 1) = wt i := by
      simpa [wt] using (ordered_length_one_weight 𝕜 L i)
    rw [hweight] at h
    exact (Nat.not_le_of_gt (adaptedCutoff_gt_weight 𝕜 L i))
      h
  intro hmem
  obtain ⟨c, hc, hceq⟩ :=
    (Finsupp.mem_span_image_iff_linearCombination 𝕜).mp hmem
  let d : (Fin (adaptedWeightedBasis 𝕜 L).n →₀ ℕ) →₀ 𝕜 :=
    ∑ j, Finsupp.single (Finsupp.single j 1) (b.repr x j)
  have hdeq : Finsupp.linearCombination 𝕜 v d =
      UniversalEnvelopingAlgebra.ι 𝕜 x := by
    calc
      Finsupp.linearCombination 𝕜 v d =
          ∑ j, b.repr x j •
            orderedPBWMonomial 𝕜 L b (Finsupp.single j 1) := by
        simp [d, v, Finsupp.linearCombination_apply]
      _ = ∑ j, b.repr x j • UniversalEnvelopingAlgebra.ι 𝕜 (b j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [orderedPBWMonomial_single]
      _ = UniversalEnvelopingAlgebra.ι 𝕜 x := hxexp.symm
  have hcd : c = d :=
    hli.finsuppLinearCombination_injective (hceq.trans hdeq.symm)
  have hci : c (Finsupp.single i 1) = 0 :=
    ((Finsupp.mem_supported' 𝕜 c).1 hc) _ hnot
  have hdi : d (Finsupp.single i 1) = b.repr x i := by
    classical
    simp only [d, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have hsingle : Finsupp.single j (1 : ℕ) ≠ Finsupp.single i 1 := by
        intro heq
        apply hji
        exact Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) heq
      rw [Finsupp.single_eq_of_ne hsingle.symm]
    · simp
  apply hi
  rw [← hdi, ← hcd]
  exact hci

/-! ### The precise conditional PBW-to-raw comparison -/

def HighWeightOrderedRewrite : Prop :=
  (nilpotentWeightedLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L)).restrictScalars 𝕜 ≤
    highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L)

lemma adaptedListWeight_ofFn {k : ℕ}
    (f : Fin k → Fin (adaptedWeightedBasis 𝕜 L).n) :
    adaptedListWeight 𝕜 L (List.ofFn f) = adaptedWordWeight 𝕜 L f := by
  simp [adaptedListWeight, adaptedWordWeight, List.map_ofFn, List.sum_ofFn]

lemma highWeightOrderedRewrite : HighWeightOrderedRewrite 𝕜 L := by
  intro u hu
  change u ∈ nilpotentWeightedLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L) at hu
  have hleft : ∀ c : U,
      c * u ∈ highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L) := by
    refine Submodule.span_induction
      (p := fun v _ => ∀ c : U,
        c * v ∈ highWeightOrderedSpan 𝕜 L (adaptedCutoff 𝕜 L))
      ?_ ?_ ?_ ?_ hu
    · rintro v ⟨a, b, k, f, hf, rfl⟩ c
      have hf' : adaptedCutoff 𝕜 L ≤
          adaptedListWeight 𝕜 L (List.ofFn f) := by
        simpa [adaptedListWeight_ofFn 𝕜 L f] using hf
      simpa [adaptedIotaWord, adaptedRawWord, Function.comp_def, mul_assoc] using
        (adaptedOrderedPBWBasis_context_mem_highWeight 𝕜 L
          (c * a) b (List.ofFn f) hf')
    · intro c
      simp
    · intro v z _ _ hv hz c
      rw [mul_add]
      exact add_mem (hv c) (hz c)
    · intro r v _ hv c
      simpa [smul_eq_mul, mul_assoc] using hv (c * r)
  simpa using hleft 1

lemma iota_not_mem_nilpotentWeightedLeftIdeal_of_PBW
    (hPBW : HasOrderedPBWBasis 𝕜 L (adaptedWeightedBasis 𝕜 L).basis)
    {x : L} (hx : x ≠ 0) :
    UniversalEnvelopingAlgebra.ι 𝕜 x ∉
      nilpotentWeightedLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L) := by
  intro hmem
  exact iota_not_mem_highWeightOrderedSpan_of_PBW 𝕜 L hPBW hx
    ((highWeightOrderedRewrite 𝕜 L) hmem)

/-! ### Conditional faithful quotient, with nilpotent action -/

lemma existsFaithfulFiniteDimensional_of_nilpotent_of_PBW
    (hPBW : HasOrderedPBWBasis 𝕜 L (adaptedWeightedBasis 𝕜 L).basis) :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule L V) (_ : LieModule 𝕜 L V),
        LieModule.IsFaithful 𝕜 L V ∧
          ∀ x : L, IsNilpotent (LieModule.toEnd 𝕜 L V x) := by
  let J := nilpotentWeightedLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L)
  letI : LieRingModule U (U ⧸ J) := LieRingModule.ofAssociativeModule
  letI : LieModule 𝕜 U (U ⧸ J) := LieModule.ofAssociativeModule
  letI : LieRingModule L (U ⧸ J) :=
    LieRingModule.compLieHom (U ⧸ J) (UniversalEnvelopingAlgebra.ι 𝕜)
  letI : LieModule 𝕜 L (U ⧸ J) :=
    LieModule.compLieHom (U ⧸ J) (UniversalEnvelopingAlgebra.ι 𝕜)
  haveI : FiniteDimensional 𝕜 (U ⧸ J) :=
    finiteDimensional_nilpotentWeightedQuotient 𝕜 L
  refine ⟨U ⧸ J, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ?_⟩
  · refine LieModule.IsFaithful.mk ?_
    intro x y hxy
    have hsub : LieModule.toEnd 𝕜 L (U ⧸ J) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hz1 :
        (LieModule.toEnd 𝕜 L (U ⧸ J) (x - y))
            (Submodule.Quotient.mk (1 : U)) = 0 := by
      rw [hsub, LinearMap.zero_apply]
    have hzJ : UniversalEnvelopingAlgebra.ι 𝕜 (x - y) ∈ J := by
      have hact :
          (LieModule.toEnd 𝕜 L (U ⧸ J) (x - y))
              (Submodule.Quotient.mk (1 : U)) =
            Submodule.Quotient.mk
              (UniversalEnvelopingAlgebra.ι 𝕜 (x - y) * (1 : U)) := rfl
      rw [hact, mul_one] at hz1
      exact (Submodule.Quotient.mk_eq_zero J).1 hz1
    apply sub_eq_zero.mp
    by_contra hxy0
    exact iota_not_mem_nilpotentWeightedLeftIdeal_of_PBW 𝕜 L hPBW
      hxy0 hzJ
  · intro x
    refine ⟨adaptedCutoff 𝕜 L, ?_⟩
    apply LinearMap.ext
    intro u
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective J u
    have hword : iotaWord 𝕜 L
          (List.ofFn fun _ : Fin (adaptedCutoff 𝕜 L) => x) ∈
        envelopingLengthLeftIdeal 𝕜 L (adaptedCutoff 𝕜 L) :=
      iotaWord_mem_envelopingLengthLeftIdeal 𝕜 L (fun _ => x)
    have hJ : iotaWord 𝕜 L
          (List.ofFn fun _ : Fin (adaptedCutoff 𝕜 L) => x) ∈ J :=
      envelopingLengthLeftIdeal_le_nilpotentWeightedLeftIdeal 𝕜 L le_rfl hword
    have hpow : (UniversalEnvelopingAlgebra.ι 𝕜 x) ^ adaptedCutoff 𝕜 L =
        iotaWord 𝕜 L
          (List.ofFn fun _ : Fin (adaptedCutoff 𝕜 L) => x) := by
      induction adaptedCutoff 𝕜 L with
      | zero => simp [iotaWord]
      | succ n ih =>
          rw [pow_succ', ih]
          simp [iotaWord, List.ofFn_succ]
    have hright :
        iotaWord 𝕜 L
            (List.ofFn fun _ : Fin (adaptedCutoff 𝕜 L) => x) * w ∈ J :=
      nilpotentWeightedLeftIdeal_right_stable 𝕜 L hJ
    have haction : ∀ n : ℕ,
        (LieModule.toEnd 𝕜 L (U ⧸ J) x ^ n)
            (Submodule.Quotient.mk (p := J) w) =
          Submodule.Quotient.mk (p := J)
            ((UniversalEnvelopingAlgebra.ι 𝕜 x) ^ n * w) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, ih]
          simp only [LieModule.toEnd_apply_apply,
            LieRingModule.compLieHom_apply, lie_eq_smul]
          rw [← Submodule.Quotient.mk_smul J]
          simp [LieRingModule.compLieHom_apply, LieModule.toEnd_apply_apply,
            lie_eq_smul, smul_eq_mul, pow_succ', mul_assoc]
    rw [haction]
    rw [hpow]
    simp only [LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero J).2 hright

end LeeNilpotentPBWWeightedBridge
