import LeeSmoothLib.Ch08.Sec08_62.NilpotentFaithfulRepresentation
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic

open scoped Pointwise Classical
open LieModule
open LeeNilpotentPBWWeightedBridge

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieRingModule.ofAssociativeModule
attribute [local instance 100] LieModule.ofAssociativeModule

universe uK uN

namespace LeeNilpotentDerivationStableRepresentation

variable (K : Type uK) [Field K] [CharZero K]
variable (N : Type uN) [LieRing N] [LieAlgebra K N] [FiniteDimensional K N]

lemma leeNilpotentDerivation_preserves_lowerCentralSeries
    [LieRing.IsNilpotent N] (D : LieDerivation K N N) (k : ℕ) {x : N}
    (hx : x ∈ lowerCentralSeries K N N k) :
    D x ∈ lowerCentralSeries K N N k := by
  induction k generalizing x with
  | zero =>
      simpa [lowerCentralSeries_zero]
  | succ k ih =>
      rw [lowerCentralSeries_succ] at hx ⊢
      change x ∈ (⁅(⊤ : LieIdeal K N), lowerCentralSeries K N N k⁆ :
        LieIdeal K N).toSubmodule at hx
      change D x ∈ (⁅(⊤ : LieIdeal K N), lowerCentralSeries K N N k⁆ :
        LieIdeal K N).toSubmodule
      rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
      refine Submodule.span_induction
        (p := fun z _ => D z ∈
          (⁅(⊤ : LieIdeal K N), lowerCentralSeries K N N k⁆ :
            LieIdeal K N).toSubmodule)
        ?_ ?_ ?_ ?_ hx
      · rintro z ⟨a, ha, b, hb, rfl⟩
        rw [D.apply_lie_eq_add]
        exact add_mem
          (LieSubmodule.lie_mem_lie ha (ih hb))
          (LieSubmodule.lie_mem_lie (show D a ∈ (⊤ : LieIdeal K N) from trivial) hb)
      · simp
      · intro u v _ _ hu hv
        rw [map_add]
        exact add_mem hu hv
      · intro r u _ hu
        rw [map_smul]
        exact SMulMemClass.smul_mem r hu

variable [LieRing.IsNilpotent N]

local notation "U" => UniversalEnvelopingAlgebra K N

noncomputable def leeSquareZeroLieHom
    (D : LieDerivation K N N) : N →ₗ⁅K⁆ TrivSqZeroExt U U := by
  letI : Algebra K (TrivSqZeroExt U U) := TrivSqZeroExt.algebra' K U U
  refine
    { toFun := fun x =>
        TrivSqZeroExt.inl (UniversalEnvelopingAlgebra.ι K x) +
          TrivSqZeroExt.inr (UniversalEnvelopingAlgebra.ι K (D x))
      map_add' := ?_
      map_smul' := ?_
      map_lie' := ?_ }
  · intro x y
    simp only [map_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel
  · intro r x
    ext
    · simp [Algebra.smul_def]
      rw [show ((algebraMap K (TrivSqZeroExt U U)) r).fst = algebraMap K U r by rfl]
    · simp [TrivSqZeroExt.algebra']
  · intro x y
    ext
    · simp [LieRing.of_associative_ring_bracket]
    · simp only [LieRing.of_associative_ring_bracket, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, zero_smul, smul_zero,
        add_zero, zero_add]
      rw [D.apply_lie_eq_add, map_add]
      rw [LieHom.map_lie (UniversalEnvelopingAlgebra.ι K) x (D y)]
      rw [LieHom.map_lie (UniversalEnvelopingAlgebra.ι K) (D x) y]
      simp [LieRing.of_associative_ring_bracket, smul_eq_mul, op_smul_eq_mul] <;>
        noncomm_ring

noncomputable def leeSquareZeroAlgHom
    (D : LieDerivation K N N) : U →ₐ[K] TrivSqZeroExt U U := by
  letI : Algebra K (TrivSqZeroExt U U) := TrivSqZeroExt.algebra' K U U
  exact UniversalEnvelopingAlgebra.lift K (leeSquareZeroLieHom K N D)

noncomputable def leeAssociativeExtension
    (D : LieDerivation K N N) : U →ₗ[K] U := by
  letI : Algebra K (TrivSqZeroExt U U) := TrivSqZeroExt.algebra' K U U
  exact
    (TrivSqZeroExt.sndHom U U).restrictScalars K |>.comp
      (leeSquareZeroAlgHom K N D).toLinearMap

lemma leeSquareZeroAlgHom_fst (D : LieDerivation K N N) (u : U) :
    (leeSquareZeroAlgHom K N D u).fst = u := by
  letI : Algebra K (TrivSqZeroExt U U) := TrivSqZeroExt.algebra' K U U
  let F := leeSquareZeroAlgHom K N D
  let base : U →ₐ[K] U :=
    { toFun := fun u => (F u).fst
      map_one' := by simp [F]
      map_mul' := by intro u v; simp [F]
      map_zero' := by simp [F]
      map_add' := by intro u v; simp [F]
      commutes' := by
        intro r
        rw [F.commutes]
        rfl }
  have hbase : base = AlgHom.id K U := by
    apply UniversalEnvelopingAlgebra.hom_ext
    ext x
    simp [base, F, leeSquareZeroAlgHom, leeSquareZeroLieHom]
  exact congrArg (fun f : U →ₐ[K] U => f u) hbase

lemma leeAssociativeExtension_mul (D : LieDerivation K N N) (u v : U) :
    leeAssociativeExtension K N D (u * v) =
      u * leeAssociativeExtension K N D v +
        leeAssociativeExtension K N D u * v := by
  letI : Algebra K (TrivSqZeroExt U U) := TrivSqZeroExt.algebra' K U U
  have h := congrArg TrivSqZeroExt.snd
    ((leeSquareZeroAlgHom K N D).map_mul u v)
  simpa [leeAssociativeExtension, TrivSqZeroExt.snd_mul,
    leeSquareZeroAlgHom_fst, smul_eq_mul, op_smul_eq_mul] using h

lemma leeAssociativeExtension_iota (D : LieDerivation K N N) (x : N) :
    leeAssociativeExtension K N D (UniversalEnvelopingAlgebra.ι K x) =
      UniversalEnvelopingAlgebra.ι K (D x) := by
  letI : Algebra K (TrivSqZeroExt U U) := TrivSqZeroExt.algebra' K U U
  simp [leeAssociativeExtension, leeSquareZeroAlgHom,
    leeSquareZeroLieHom]

lemma leeAssociativeExtension_one (D : LieDerivation K N N) :
    leeAssociativeExtension K N D 1 = 0 := by
  letI : Algebra K (TrivSqZeroExt U U) := TrivSqZeroExt.algebra' K U U
  simp [leeAssociativeExtension, leeSquareZeroAlgHom]

lemma leeAssociativeExtension_eq_of_eq_on_iota
    (f g : U →ₗ[K] U)
    (hf1 : f 1 = 0) (hg1 : g 1 = 0)
    (hfmul : ∀ a b, f (a * b) = a * f b + f a * b)
    (hgmul : ∀ a b, g (a * b) = a * g b + g a * b)
    (hι : ∀ x : N,
      f (UniversalEnvelopingAlgebra.ι K x) =
        g (UniversalEnvelopingAlgebra.ι K x)) :
    f = g := by
  apply LinearMap.ext
  intro u
  refine TauCeti.UniversalEnvelopingAlgebra.induction_ι K N
    (ι := fun x => hι x)
    (algebraMap := ?_)
    (add := ?_)
    (mul := ?_)
    u
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, hf1, hg1]
  · intro a b ha hb
    simp only [map_add, ha, hb]
  · intro a b ha hb
    rw [hfmul a b, hgmul a b, ha, hb]

lemma leeAssociativeExtension_zero :
    leeAssociativeExtension K N (0 : LieDerivation K N N) = 0 := by
  apply leeAssociativeExtension_eq_of_eq_on_iota K N
    (leeAssociativeExtension K N (0 : LieDerivation K N N)) 0
  · simp [leeAssociativeExtension_one]
  · simp
  · intro a b
    rw [leeAssociativeExtension_mul]
  · intro a b
    simp
  · intro x
    simpa [UniversalEnvelopingAlgebra.ι_apply] using
      (leeAssociativeExtension_iota K N (0 : LieDerivation K N N) x)

lemma leeAssociativeExtension_add (D E : LieDerivation K N N) :
    leeAssociativeExtension K N (D + E) =
      leeAssociativeExtension K N D + leeAssociativeExtension K N E := by
  apply leeAssociativeExtension_eq_of_eq_on_iota K N
    (leeAssociativeExtension K N (D + E))
    (leeAssociativeExtension K N D + leeAssociativeExtension K N E)
  · simp [leeAssociativeExtension_one]
  · simp [leeAssociativeExtension_one]
  · intro a b
    rw [leeAssociativeExtension_mul]
  · intro a b
    simp only [LinearMap.add_apply]
    rw [leeAssociativeExtension_mul, leeAssociativeExtension_mul]
    noncomm_ring
  · intro x
    change leeAssociativeExtension K N (D + E)
        (UniversalEnvelopingAlgebra.ι K x) =
      leeAssociativeExtension K N D (UniversalEnvelopingAlgebra.ι K x) +
        leeAssociativeExtension K N E (UniversalEnvelopingAlgebra.ι K x)
    rw [leeAssociativeExtension_iota, leeAssociativeExtension_iota,
      leeAssociativeExtension_iota]
    simp

lemma leeAssociativeExtension_smul (r : K) (D : LieDerivation K N N) :
    leeAssociativeExtension K N (r • D) =
      r • leeAssociativeExtension K N D := by
  apply leeAssociativeExtension_eq_of_eq_on_iota K N
    (leeAssociativeExtension K N (r • D))
    (r • leeAssociativeExtension K N D)
  · simp [leeAssociativeExtension_one]
  · simp [leeAssociativeExtension_one]
  · intro a b
    rw [leeAssociativeExtension_mul]
  · intro a b
    simp only [LinearMap.smul_apply]
    rw [leeAssociativeExtension_mul]
    simp only [Algebra.smul_def, mul_add, add_mul]
    calc
      (algebraMap K U r) * (a * leeAssociativeExtension K N D b) +
          (algebraMap K U r) * (leeAssociativeExtension K N D a * b) =
        (algebraMap K U r) * (leeAssociativeExtension K N D a * b) +
          (algebraMap K U r) * (a * leeAssociativeExtension K N D b) :=
            add_comm _ _
      _ = (algebraMap K U r) * (leeAssociativeExtension K N D a * b) +
          a * ((algebraMap K U r) * leeAssociativeExtension K N D b) := by
        have hcomm :
            (algebraMap K U r) * (a * leeAssociativeExtension K N D b) =
              a * ((algebraMap K U r) * leeAssociativeExtension K N D b) := by
          rw [← mul_assoc, Algebra.commutes, mul_assoc]
        rw [hcomm]
      _ = a * ((algebraMap K U r) * leeAssociativeExtension K N D b) +
          (algebraMap K U r) * (leeAssociativeExtension K N D a * b) :=
        add_comm _ _
      _ = a * ((algebraMap K U r) * leeAssociativeExtension K N D b) +
          ((algebraMap K U r) * leeAssociativeExtension K N D a) * b := by
        rw [mul_assoc]
  · intro x
    change leeAssociativeExtension K N (r • D)
        (UniversalEnvelopingAlgebra.ι K x) =
      (r • leeAssociativeExtension K N D)
        (UniversalEnvelopingAlgebra.ι K x)
    rw [leeAssociativeExtension_iota, LinearMap.smul_apply,
      leeAssociativeExtension_iota]
    simp [LieDerivation.smul_apply]

lemma leeAssociativeExtension_commutator_mul
    (D E : LieDerivation K N N) (a b : U) :
    (⁅leeAssociativeExtension K N D, leeAssociativeExtension K N E⁆ :
        Module.End K U) (a * b) =
      a * (⁅leeAssociativeExtension K N D, leeAssociativeExtension K N E⁆ :
        Module.End K U) b +
        (⁅leeAssociativeExtension K N D, leeAssociativeExtension K N E⁆ :
          Module.End K U) a * b := by
  change
    leeAssociativeExtension K N D
          (leeAssociativeExtension K N E (a * b)) -
        leeAssociativeExtension K N E
          (leeAssociativeExtension K N D (a * b)) =
      a * (leeAssociativeExtension K N D
          (leeAssociativeExtension K N E b) -
        leeAssociativeExtension K N E
          (leeAssociativeExtension K N D b)) +
        (leeAssociativeExtension K N D
          (leeAssociativeExtension K N E a) -
        leeAssociativeExtension K N E
          (leeAssociativeExtension K N D a)) * b
  simp only [leeAssociativeExtension_mul, map_add]
  noncomm_ring

lemma leeAssociativeExtension_lie (D E : LieDerivation K N N) :
    leeAssociativeExtension K N ⁅D, E⁆ =
      ⁅leeAssociativeExtension K N D, leeAssociativeExtension K N E⁆ := by
  apply leeAssociativeExtension_eq_of_eq_on_iota K N
    (leeAssociativeExtension K N ⁅D, E⁆)
    (⁅leeAssociativeExtension K N D, leeAssociativeExtension K N E⁆ :
      Module.End K U)
  · simp [leeAssociativeExtension_one]
  · simp [leeAssociativeExtension_one]
  · intro a b
    exact leeAssociativeExtension_mul K N ⁅D, E⁆ a b
  · intro a b
    exact leeAssociativeExtension_commutator_mul K N D E a b
  · intro x
    change leeAssociativeExtension K N ⁅D, E⁆
        (UniversalEnvelopingAlgebra.ι K x) =
      (⁅leeAssociativeExtension K N D, leeAssociativeExtension K N E⁆ :
        Module.End K U) (UniversalEnvelopingAlgebra.ι K x)
    rw [leeAssociativeExtension_iota]
    change UniversalEnvelopingAlgebra.ι K (⁅D, E⁆ x) =
      leeAssociativeExtension K N D
          (leeAssociativeExtension K N E (UniversalEnvelopingAlgebra.ι K x)) -
        leeAssociativeExtension K N E
          (leeAssociativeExtension K N D (UniversalEnvelopingAlgebra.ι K x))
    rw [LieDerivation.commutator_apply, leeAssociativeExtension_iota,
      leeAssociativeExtension_iota, leeAssociativeExtension_iota]
    rw [leeAssociativeExtension_iota]
    simp

noncomputable def leeAssociativeExtensionLieHom :
    LieDerivation K N N →ₗ⁅K⁆ Module.End K U :=
  { toFun := fun D => leeAssociativeExtension K N D
    map_add' := fun D E => leeAssociativeExtension_add K N D E
    map_smul' := fun r D => leeAssociativeExtension_smul K N r D
    map_lie' := by
      intro D E
      exact leeAssociativeExtension_lie K N D E }

lemma leeRawWord_context_mem_nilpotentWeightedLeftIdeal
    (p w q : List (Fin (adaptedWeightedBasis K N).n))
    (hw : adaptedCutoff K N ≤ adaptedListWeight K N (p ++ w ++ q)) :
    adaptedRawWord K N p * adaptedRawWord K N w * adaptedRawWord K N q ∈
      nilpotentWeightedLeftIdeal K N (adaptedCutoff K N) := by
  let t := p ++ w ++ q
  let f : Fin t.length → Fin (adaptedWeightedBasis K N).n := t.get
  have hf : List.ofFn f = t := by
    exact List.ofFn_get t
  have hweight : adaptedWordWeight K N f = adaptedListWeight K N t := by
    simp [f, adaptedWordWeight, adaptedListWeight, ← Fin.sum_univ_fun_getElem]
  have hmap :
      List.ofFn (fun i : Fin t.length =>
        (adaptedWeightedBasis K N).basis (t.get i)) =
        t.map (adaptedWeightedBasis K N).basis := by
    simpa using
      (List.ofFn_getElem_eq_map t (adaptedWeightedBasis K N).basis)
  apply Submodule.subset_span
  refine ⟨1, 1, t.length, f,
    ?_, ?_⟩
  · simpa [t, hweight, adaptedListWeight, List.append_assoc] using hw
  · rw [show adaptedIotaWord K N f =
        LeeAdoWeightedTruncation.iotaWord K N
          (t.map (adaptedWeightedBasis K N).basis) by
          simp only [adaptedIotaWord, f]
          rw [hmap]]
    simp [t, adaptedRawWord, LeeAdoWeightedTruncation.iotaWord,
      List.map_append, List.prod_append, List.append_assoc, mul_assoc]

lemma leeDerivation_adaptedBasis_weight_support
    (D : LieDerivation K N N)
    (i j : Fin (adaptedWeightedBasis K N).n)
    (hcoef : (adaptedWeightedBasis K N).basis.repr
        (D ((adaptedWeightedBasis K N).basis i)) j ≠ 0) :
    (adaptedWeightedBasis K N).wt i ≤
      (adaptedWeightedBasis K N).wt j := by
  have hmem : D ((adaptedWeightedBasis K N).basis i) ∈
    lcsSub K N ((adaptedWeightedBasis K N).wt i - 1) := by
    exact leeNilpotentDerivation_preserves_lowerCentralSeries K N D
      ((adaptedWeightedBasis K N).wt i - 1)
      (adaptedWeightedBasis_basis_mem_lcs K N i)
  have hlt := adapted_repr_support_of_lcs K N
    hmem j hcoef
  omega

lemma leeAssociativeExtension_raw_context_mem_nilpotentWeightedLeftIdeal
    (D : LieDerivation K N N)
    (p s q : List (Fin (adaptedWeightedBasis K N).n))
    (hN : adaptedCutoff K N ≤
      adaptedListWeight K N (p ++ s ++ q)) :
    adaptedRawWord K N p *
          leeAssociativeExtension K N D (adaptedRawWord K N s) *
        adaptedRawWord K N q ∈
      nilpotentWeightedLeftIdeal K N (adaptedCutoff K N) := by
  induction s generalizing p with
  | nil =>
      simp [adaptedRawWord, LeeAdoWeightedTruncation.iotaWord,
        leeAssociativeExtension_one]
  | cons i s ih =>
      have hraw : adaptedRawWord K N (i :: s) =
          UniversalEnvelopingAlgebra.ι K
              ((adaptedWeightedBasis K N).basis i) *
            adaptedRawWord K N s := by
        simp [adaptedRawWord, LeeAdoWeightedTruncation.iotaWord,
          List.map_cons, List.prod_cons]
      rw [hraw, leeAssociativeExtension_mul, mul_add, add_mul]
      apply add_mem
      · have hNfirst : adaptedCutoff K N ≤
            adaptedListWeight K N (p ++ [i] ++ s ++ q) := by
          simpa [adaptedListWeight, List.append_assoc] using hN
        simpa [adaptedRawWord, LeeAdoWeightedTruncation.iotaWord,
          List.map_append, List.prod_append, mul_assoc] using
          (ih (p ++ [i]) hNfirst)
      · rw [leeAssociativeExtension_iota, adapted_iota_repr_sum]
        rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_mul]
        refine sum_mem fun j _ => ?_
        let c := (adaptedWeightedBasis K N).basis.repr
          (D ((adaptedWeightedBasis K N).basis i)) j
        by_cases hc : c = 0
        · simp [c, hc]
        · have hwt := leeDerivation_adaptedBasis_weight_support K N D i j hc
          have hN' : adaptedCutoff K N ≤
              adaptedListWeight K N p +
                (adaptedWeightedBasis K N).wt i +
                adaptedListWeight K N s + adaptedListWeight K N q := by
            simpa [adaptedListWeight, List.append_assoc, add_assoc] using hN
          have htotal : adaptedCutoff K N ≤
              adaptedListWeight K N (p ++ [j] ++ s ++ q) := by
            have hN'' : adaptedCutoff K N ≤
                adaptedListWeight K N p +
                  (adaptedWeightedBasis K N).wt j +
                  adaptedListWeight K N s + adaptedListWeight K N q := by
              omega
            simpa [adaptedListWeight, List.append_assoc, add_assoc] using hN''
          have hraw' := leeRawWord_context_mem_nilpotentWeightedLeftIdeal
            K N p ([j] ++ s) q (by
              simpa [List.append_assoc] using htotal)
          have hsmul :=
            (nilpotentWeightedLeftIdeal K N (adaptedCutoff K N)).smul_mem
              (algebraMap K U c) hraw'
          convert hsmul using 1
          simp only [c, adaptedRawWord, LeeAdoWeightedTruncation.iotaWord,
            List.map_cons, List.map_append, List.prod_cons, List.prod_append,
            List.map_nil, List.prod_nil, one_mul, mul_one,
            Algebra.smul_def, mul_assoc,
            mul_smul_comm, smul_mul_assoc, smul_eq_mul]
          rw [← mul_assoc, ← Algebra.commutes, mul_assoc]

lemma leeAssociativeExtension_mem_nilpotentWeightedLeftIdeal
    (D : LieDerivation K N N) {u : U}
    (hu : u ∈ nilpotentWeightedLeftIdeal K N (adaptedCutoff K N)) :
    leeAssociativeExtension K N D u ∈
      nilpotentWeightedLeftIdeal K N (adaptedCutoff K N) := by
  refine Submodule.span_induction
    (p := fun u _ => leeAssociativeExtension K N D u ∈
      nilpotentWeightedLeftIdeal K N (adaptedCutoff K N))
    ?_ ?_ ?_ ?_ hu
  · rintro u ⟨a, b, k, f, hw, rfl⟩
    let s : List (Fin (adaptedWeightedBasis K N).n) := List.ofFn f
    have hsweight : adaptedListWeight K N s = adaptedWordWeight K N f := by
      simpa [s, adaptedListWeight, adaptedWordWeight, Function.comp_def] using
        (List.sum_ofFn
          (f := fun x : Fin k =>
            (adaptedWeightedBasis K N).wt (f x)))
    have hword : adaptedRawWord K N s ∈
        nilpotentWeightedLeftIdeal K N (adaptedCutoff K N) := by
      have h := leeRawWord_context_mem_nilpotentWeightedLeftIdeal
        K N ([] : List (Fin (adaptedWeightedBasis K N).n)) s [] (by
          simpa [hsweight] using hw)
      simpa [s, adaptedRawWord, adaptedIotaWord,
        LeeAdoWeightedTruncation.iotaWord] using h
    have hDword : leeAssociativeExtension K N D (adaptedRawWord K N s) ∈
        nilpotentWeightedLeftIdeal K N (adaptedCutoff K N) := by
      simpa [adaptedRawWord, LeeAdoWeightedTruncation.iotaWord, one_mul,
        mul_one] using
        (leeAssociativeExtension_raw_context_mem_nilpotentWeightedLeftIdeal
          K N D [] s [] (by simpa [hsweight] using hw))
    rw [show adaptedIotaWord K N f = adaptedRawWord K N s by
      simp [s, adaptedIotaWord, adaptedRawWord,
        LeeAdoWeightedTruncation.iotaWord, Function.comp_def]]
    rw [leeAssociativeExtension_mul, leeAssociativeExtension_mul, add_mul]
    apply add_mem
    · apply nilpotentWeightedLeftIdeal_right_stable K N
      apply nilpotentWeightedLeftIdeal_left_stable K N
      exact hword
    · apply add_mem
      · apply nilpotentWeightedLeftIdeal_right_stable K N
        apply nilpotentWeightedLeftIdeal_left_stable K N
        exact hDword
      · apply nilpotentWeightedLeftIdeal_right_stable K N
        apply nilpotentWeightedLeftIdeal_left_stable K N
        exact hword
  · simp
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro r u hmem hu
    rw [smul_eq_mul, leeAssociativeExtension_mul]
    exact add_mem
      (nilpotentWeightedLeftIdeal_left_stable K N hu)
      (nilpotentWeightedLeftIdeal_left_stable K N hmem)

noncomputable def leeNilpotentWeightedSubmodule : Submodule K U :=
  (nilpotentWeightedLeftIdeal K N (adaptedCutoff K N)).restrictScalars K

local notation "V" => U ⧸ leeNilpotentWeightedSubmodule K N

lemma leeWeightedQuotient_finiteDimensional : FiniteDimensional K V := by
  simpa [leeNilpotentWeightedSubmodule] using
    (finiteDimensional_nilpotentWeightedQuotient K N)

noncomputable def leeWeightedLeftActionInvariant :
    U →ₗ[K]
      Submodule.compatibleMaps (leeNilpotentWeightedSubmodule K N)
        (leeNilpotentWeightedSubmodule K N) := by
  let mulLeftMap : U →ₗ[K] U →ₗ[K] U :=
    { toFun := LinearMap.mulLeft K
      map_add' := by
        intro a b
        ext u
        simp [add_mul]
      map_smul' := by
        intro r a
        ext u
        simp [Algebra.smul_def] }
  refine LinearMap.codRestrict _ mulLeftMap ?_
  intro a u hu
  change a * u ∈ nilpotentWeightedLeftIdeal K N (adaptedCutoff K N)
  exact nilpotentWeightedLeftIdeal_left_stable K N hu

noncomputable def leeWeightedLeftAction :
    U →ₗ[K] Module.End K (U ⧸ leeNilpotentWeightedSubmodule K N) :=
  (Submodule.mapQLinear (leeNilpotentWeightedSubmodule K N)
      (leeNilpotentWeightedSubmodule K N)).comp
    (leeWeightedLeftActionInvariant K N)

lemma leeWeightedLeftAction_apply (a u : U) :
    leeWeightedLeftAction K N a (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (a * u) := by
  simp [leeWeightedLeftAction, leeWeightedLeftActionInvariant,
    Submodule.mapQLinear, LinearMap.mulLeft_apply]

noncomputable def leeWeightedLeftActionLieHom :
    U →ₗ⁅K⁆ Module.End K (U ⧸ leeNilpotentWeightedSubmodule K N) :=
  { toFun := leeWeightedLeftAction K N
    map_add' := by intro a b; exact (leeWeightedLeftAction K N).map_add a b
    map_smul' := by
      intro r a
      simpa using (leeWeightedLeftAction K N).map_smul r a
    map_lie' := by
      intro a b
      apply LinearMap.ext
      intro x
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective
        (leeNilpotentWeightedSubmodule K N) x
      rw [LieRing.of_associative_ring_bracket,
        LieRing.of_associative_ring_bracket]
      change
        (leeWeightedLeftAction K N (a * b - b * a))
            (Submodule.Quotient.mk u) =
          (leeWeightedLeftAction K N a)
              ((leeWeightedLeftAction K N b) (Submodule.Quotient.mk u)) -
            (leeWeightedLeftAction K N b)
              ((leeWeightedLeftAction K N a) (Submodule.Quotient.mk u))
      simp only [leeWeightedLeftAction_apply, sub_mul, mul_sub, mul_assoc]
      rfl }

noncomputable def leeQuotientDerivation
    (D : LieDerivation K N N) :
    (U ⧸ leeNilpotentWeightedSubmodule K N) →ₗ[K]
      (U ⧸ leeNilpotentWeightedSubmodule K N) :=
  (Submodule.mapQLinear (leeNilpotentWeightedSubmodule K N)
      (leeNilpotentWeightedSubmodule K N)).comp
    (by
      refine LinearMap.codRestrict _
        (leeAssociativeExtensionLieHom K N).toLinearMap ?_
      intro D u hu
      exact leeAssociativeExtension_mem_nilpotentWeightedLeftIdeal K N D hu)
    D

lemma leeQuotientDerivation_apply (D : LieDerivation K N N) (u : U) :
    leeQuotientDerivation K N D (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (leeAssociativeExtension K N D u) := by
  rfl

noncomputable def leeWeightedRho :
    N →ₗ⁅K⁆ Module.End K (U ⧸ leeNilpotentWeightedSubmodule K N) :=
  (leeWeightedLeftActionLieHom K N).comp (UniversalEnvelopingAlgebra.ι K)

@[reducible]
noncomputable def leeWeightedQuotientLieRingModule : LieRingModule N V :=
  LieRingModule.compLieHom V (leeWeightedRho K N)

attribute [local instance 100] leeWeightedQuotientLieRingModule

@[reducible]
noncomputable def leeWeightedQuotientLieModule : LieModule K N V :=
  LieModule.compLieHom V (leeWeightedRho K N)

attribute [local instance 100] leeWeightedQuotientLieModule

lemma leeWeightedRho_isFaithful : LieModule.IsFaithful K N V := by
  refine ⟨?_⟩
  intro x y hxy
  change leeWeightedRho K N x = leeWeightedRho K N y at hxy
  have hsub : leeWeightedRho K N (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hz1 : leeWeightedRho K N (x - y) (Submodule.Quotient.mk (1 : U)) = 0 := by
    rw [hsub, LinearMap.zero_apply]
  have hzJ : UniversalEnvelopingAlgebra.ι K (x - y) ∈
      nilpotentWeightedLeftIdeal K N (adaptedCutoff K N) := by
    rw [show leeWeightedRho K N (x - y) =
        leeWeightedLeftAction K N (UniversalEnvelopingAlgebra.ι K (x - y)) by rfl,
      leeWeightedLeftAction_apply, mul_one] at hz1
    have hzJ' : UniversalEnvelopingAlgebra.ι K (x - y) ∈
        leeNilpotentWeightedSubmodule K N :=
      (Submodule.Quotient.mk_eq_zero (leeNilpotentWeightedSubmodule K N)).mp hz1
    exact hzJ'
  apply sub_eq_zero.mp
  by_contra hxy0
  exact iota_not_mem_nilpotentWeightedLeftIdeal_of_PBW K N
      (realPBW_hasOrderedPBWBasis K N) hxy0 hzJ

noncomputable def leeQuotientDerivationLieHom :
    LieDerivation K N N →ₗ⁅K⁆
      Module.End K (U ⧸ leeNilpotentWeightedSubmodule K N) :=
  { toFun := leeQuotientDerivation K N
    map_add' := by
      intro D E
      apply LinearMap.ext
      intro x
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective
        (leeNilpotentWeightedSubmodule K N) x
      rw [leeQuotientDerivation_apply, LinearMap.add_apply,
        leeQuotientDerivation_apply, leeQuotientDerivation_apply,
        ← Submodule.Quotient.mk_add]
      exact congrArg Submodule.Quotient.mk
        (congrArg (fun f : U →ₗ[K] U => f u)
          (leeAssociativeExtension_add K N D E))
    map_smul' := by
      intro r D
      apply LinearMap.ext
      intro x
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective
        (leeNilpotentWeightedSubmodule K N) x
      rw [leeQuotientDerivation_apply, LinearMap.smul_apply,
        leeQuotientDerivation_apply, ← Submodule.Quotient.mk_smul]
      simp only [RingHom.id_apply]
      exact congrArg Submodule.Quotient.mk
        (congrArg (fun f : U →ₗ[K] U => f u)
          (leeAssociativeExtension_smul K N r D))
    map_lie' := by
      intro D E
      apply LinearMap.ext
      intro x
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective
        (leeNilpotentWeightedSubmodule K N) x
      rw [LieRing.of_associative_ring_bracket]
      simp only [Module.End.mul_apply, LinearMap.sub_apply]
      change
        leeQuotientDerivation K N ⁅D, E⁆ (Submodule.Quotient.mk u) =
          leeQuotientDerivation K N D
              (leeQuotientDerivation K N E (Submodule.Quotient.mk u)) -
            leeQuotientDerivation K N E
              (leeQuotientDerivation K N D (Submodule.Quotient.mk u))
      rw [leeQuotientDerivation_apply, leeQuotientDerivation_apply,
        leeQuotientDerivation_apply, leeQuotientDerivation_apply,
        leeQuotientDerivation_apply]
      have h := congrArg (fun f : U →ₗ[K] U => f u)
        (leeAssociativeExtension_lie K N D E)
      simpa [LieRing.of_associative_ring_bracket, Module.End.mul_apply,
        map_sub, Submodule.Quotient.mk_sub] using
        congrArg Submodule.Quotient.mk h }

lemma leeQuotientDerivation_commutator_rho
    (D : LieDerivation K N N) (n : N) :
    ⁅leeQuotientDerivationLieHom K N D, leeWeightedRho K N n⁆ =
      leeWeightedRho K N (D n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective
    (leeNilpotentWeightedSubmodule K N) x
  rw [LieRing.of_associative_ring_bracket]
  change
    leeQuotientDerivation K N D
          ((leeWeightedRho K N n) (Submodule.Quotient.mk u)) -
        (leeWeightedRho K N n)
          (leeQuotientDerivation K N D (Submodule.Quotient.mk u)) =
      (leeWeightedRho K N (D n)) (Submodule.Quotient.mk u)
  rw [show leeWeightedRho K N n =
      leeWeightedLeftAction K N (UniversalEnvelopingAlgebra.ι K n) by rfl]
  rw [show leeWeightedRho K N (D n) =
      leeWeightedLeftAction K N (UniversalEnvelopingAlgebra.ι K (D n)) by rfl]
  rw [leeWeightedLeftAction_apply, leeQuotientDerivation_apply,
    leeQuotientDerivation_apply, leeWeightedLeftAction_apply,
    leeWeightedLeftAction_apply]
  rw [leeAssociativeExtension_mul, leeAssociativeExtension_iota]
  simp [Submodule.Quotient.mk_sub, sub_mul, mul_assoc]

theorem existsFaithfulFiniteDimensionalNilpotentRepresentationWithDerivations :
    ∃ (W : Type (max uK uN)) (_ : AddCommGroup W) (_ : Module K W)
      (_ : FiniteDimensional K W) (_ : LieRingModule N W) (_ : LieModule K N W),
        LieModule.IsFaithful K N W ∧
          ∃ delta : LieDerivation K N N →ₗ⁅K⁆ Module.End K W,
            ∀ D n,
              ⁅delta D, LieModule.toEnd K N W n⁆ =
                LieModule.toEnd K N W (D n) := by
  haveI : FiniteDimensional K V := leeWeightedQuotient_finiteDimensional K N
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, leeWeightedRho_isFaithful K N, ?_⟩
  refine ⟨leeQuotientDerivationLieHom K N, ?_⟩
  intro D n
  exact leeQuotientDerivation_commutator_rho K N D n

end LeeNilpotentDerivationStableRepresentation
