import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Multiset.Sort
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import LeeSmoothLib.Ch08.Sec08_62.AdoNilpotent

/-!
Weighted finite-codimension left ideals in `U(L)`.

TauCeti `Ordered` supplies spanning of the unweighted PBW filtration. That is not independence.
The remaining Ado interface is that a nonzero degree-one generator does not lie in the
LCS-weighted left ideal. Unweighted length truncation cannot detect class ≥ 3 commutators.

Proved here without independence: spanning of `T(L)` by pure tensors; finite-dimensionality of
length and LCS-weighted truncated quotients; the truncated quotient is an ambient `L`-module.
Class ≤ 2 of the degree-one interface is proved via the two-step enveloping map.
-/

universe u𝕜 u𝔤

attribute [local instance 100] LieRing.ofAssociativeRing

open scoped Pointwise Classical
open LieModule

namespace LeeAdoWeightedTruncation

variable (𝕜 : Type u𝕜) [Field 𝕜] [CharZero 𝕜]
variable (L : Type u𝔤) [LieRing L] [LieAlgebra 𝕜 L]

local notation "T" => TensorAlgebra 𝕜 L
local notation "U" => UniversalEnvelopingAlgebra 𝕜 L

/-! ### Pure tensors span `T(L)` -/

lemma tprod_append {n m : ℕ} (xs : Fin n → L) (ys : Fin m → L) :
    TensorAlgebra.tprod 𝕜 L (n + m) (Fin.append xs ys) =
      TensorAlgebra.tprod 𝕜 L n xs * TensorAlgebra.tprod 𝕜 L m ys := by
  simp only [TensorAlgebra.tprod_apply]
  rw [List.ofFn_comp' (Fin.append xs ys) (TensorAlgebra.ι 𝕜), List.ofFn_fin_append,
    List.map_append, List.prod_append]
  simp [Function.comp_def]

def allTprods : Set T :=
  ⋃ n : ℕ, Set.range (TensorAlgebra.tprod 𝕜 L n)

lemma tprod_mem_allTprods {n : ℕ} (xs : Fin n → L) :
    TensorAlgebra.tprod 𝕜 L n xs ∈ allTprods 𝕜 L :=
  Set.mem_iUnion.2 ⟨n, Set.mem_range_self xs⟩

lemma one_mem_allTprods : (1 : T) ∈ allTprods 𝕜 L := by
  simpa [TensorAlgebra.tprod_apply] using
    tprod_mem_allTprods 𝕜 L (fun _ : Fin 0 => (0 : L))

lemma allTprods_mul_subset : allTprods 𝕜 L * allTprods 𝕜 L ⊆ allTprods 𝕜 L := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  obtain ⟨xs, rfl⟩ := hn
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hy
  obtain ⟨ys, rfl⟩ := hm
  change TensorAlgebra.tprod 𝕜 L n xs * TensorAlgebra.tprod 𝕜 L m ys ∈ allTprods 𝕜 L
  rw [← tprod_append]
  exact tprod_mem_allTprods 𝕜 L (Fin.append xs ys)

lemma span_allTprods_eq_top : Submodule.span 𝕜 (allTprods 𝕜 L) = ⊤ := by
  have hmul :
      Submodule.span 𝕜 (allTprods 𝕜 L) * Submodule.span 𝕜 (allTprods 𝕜 L) ≤
        Submodule.span 𝕜 (allTprods 𝕜 L) := by
    rw [Submodule.span_mul_span]
    exact Submodule.span_mono (allTprods_mul_subset 𝕜 L)
  refine Submodule.eq_top_iff'.2 fun x => ?_
  induction x using TensorAlgebra.induction with
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ r (Submodule.subset_span (one_mem_allTprods 𝕜 L))
  | ι y =>
      simpa [TensorAlgebra.tprod_apply] using
        Submodule.subset_span (tprod_mem_allTprods 𝕜 L (fun _ : Fin 1 => y))
  | add a b ha hb => exact add_mem ha hb
  | mul a b ha hb => exact hmul (Submodule.mul_mem_mul ha hb)

/-! ### Length left ideal of `T(L)` -/

noncomputable def tensorLengthLeftIdeal (n : ℕ) : Submodule T T :=
  Submodule.span T (Set.range fun xs : Fin n → L => TensorAlgebra.tprod 𝕜 L n xs)

lemma tprod_mem_tensorLengthLeftIdeal {n : ℕ} (xs : Fin n → L) :
    TensorAlgebra.tprod 𝕜 L n xs ∈ tensorLengthLeftIdeal 𝕜 L n :=
  Submodule.subset_span ⟨xs, rfl⟩

lemma tprod_cons_eq {n : ℕ} (x : L) (ys : Fin n → L) :
    TensorAlgebra.tprod 𝕜 L (n + 1) (Fin.cons x ys) =
      TensorAlgebra.ι 𝕜 x * TensorAlgebra.tprod 𝕜 L n ys := by
  simp [TensorAlgebra.tprod_apply, List.ofFn_succ, List.prod_cons]

lemma tprod_mem_tensorLengthLeftIdeal_of_le {n k : ℕ} (h : n ≤ k) (xs : Fin k → L) :
    TensorAlgebra.tprod 𝕜 L k xs ∈ tensorLengthLeftIdeal 𝕜 L n := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  subst hd
  induction d with
  | zero =>
      simpa using tprod_mem_tensorLengthLeftIdeal 𝕜 L xs
  | succ d ih =>
      have hx : xs = Fin.cons (xs 0) (Fin.tail xs) := (Fin.cons_self_tail xs).symm
      rw [hx]
      have : TensorAlgebra.tprod 𝕜 L (n + (d + 1)) (Fin.cons (xs 0) (Fin.tail xs)) =
          TensorAlgebra.ι 𝕜 (xs 0) * TensorAlgebra.tprod 𝕜 L (n + d) (Fin.tail xs) := by
        simp [TensorAlgebra.tprod_apply, List.ofFn_succ, Fin.tail]
      rw [this]
      exact Submodule.smul_mem _ _ (ih (Nat.le_add_right n d) (Fin.tail xs))

def longTprods (n : ℕ) : Set T :=
  {t | ∃ (k : ℕ) (_ : n ≤ k) (xs : Fin k → L), t = TensorAlgebra.tprod 𝕜 L k xs}

def tensorHighSpan (n : ℕ) : Submodule 𝕜 T :=
  Submodule.span 𝕜 (longTprods 𝕜 L n)

lemma tensorHighSpan_le_lengthIdeal (n : ℕ) :
    tensorHighSpan 𝕜 L n ≤ (tensorLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜 := by
  refine Submodule.span_le.2 ?_
  rintro t ⟨k, hk, xs, rfl⟩
  exact tprod_mem_tensorLengthLeftIdeal_of_le 𝕜 L hk xs

/-! ### Short basis words -/

variable [FiniteDimensional 𝕜 L]

noncomputable def basisIndex : ℕ := Module.finrank 𝕜 L

noncomputable def finBasisL : Module.Basis (Fin (basisIndex 𝕜 L)) 𝕜 L :=
  Module.finBasis 𝕜 L

def shortBasisTprods (n : ℕ) : Set T :=
  ⋃ k : Fin n, Set.range fun f : Fin k.val → Fin (basisIndex 𝕜 L) =>
    TensorAlgebra.tprod 𝕜 L k.val fun i => finBasisL 𝕜 L (f i)

lemma shortBasisTprods_finite (n : ℕ) : (shortBasisTprods 𝕜 L n).Finite :=
  Set.finite_iUnion fun _ => Set.finite_range _

def tensorLowSpan (n : ℕ) : Submodule 𝕜 T :=
  Submodule.span 𝕜 (shortBasisTprods 𝕜 L n)

lemma tprod_basis_mem_low {n k : ℕ} (hk : k < n) (f : Fin k → Fin (basisIndex 𝕜 L)) :
    TensorAlgebra.tprod 𝕜 L k (fun i => finBasisL 𝕜 L (f i)) ∈ tensorLowSpan 𝕜 L n :=
  Submodule.subset_span <| Set.mem_iUnion.2 ⟨⟨k, hk⟩, Set.mem_range_self f⟩

lemma tprod_eq_sum_basis_tprod {k : ℕ} (xs : Fin k → L) :
    TensorAlgebra.tprod 𝕜 L k xs =
      ∑ f : Fin k → Fin (basisIndex 𝕜 L),
        (∏ i, (finBasisL 𝕜 L).repr (xs i) (f i)) •
          TensorAlgebra.tprod 𝕜 L k (fun i => finBasisL 𝕜 L (f i)) := by
  let xs' : Fin k → L := fun i => ∑ j, (finBasisL 𝕜 L).repr (xs i) j • finBasisL 𝕜 L j
  have hxs : xs = xs' := by
    ext i
    exact ((finBasisL 𝕜 L).sum_repr (xs i)).symm
  rw [hxs]
  rw [MultilinearMap.map_sum (TensorAlgebra.tprod 𝕜 L k)
    (g := fun i j => (finBasisL 𝕜 L).repr (xs i) j • finBasisL 𝕜 L j)]
  refine Finset.sum_congr rfl fun f _ => ?_
  simpa [xs'] using (TensorAlgebra.tprod 𝕜 L k).map_smul_univ
    (fun i => (finBasisL 𝕜 L).repr (xs i) (f i))
    (fun i => finBasisL 𝕜 L (f i))

lemma tprod_mem_low_of_lt {n k : ℕ} (hk : k < n) (xs : Fin k → L) :
    TensorAlgebra.tprod 𝕜 L k xs ∈ tensorLowSpan 𝕜 L n := by
  rw [tprod_eq_sum_basis_tprod]
  exact sum_mem fun f _ =>
    Submodule.smul_mem (tensorLowSpan 𝕜 L n) _ (tprod_basis_mem_low 𝕜 L hk f)

lemma tprod_mem_low_or_high {n k : ℕ} (xs : Fin k → L) :
    TensorAlgebra.tprod 𝕜 L k xs ∈ tensorLowSpan 𝕜 L n ⊔ tensorHighSpan 𝕜 L n := by
  by_cases hk : k < n
  · have hx : TensorAlgebra.tprod 𝕜 L k xs ∈ tensorLowSpan 𝕜 L n :=
      tprod_mem_low_of_lt 𝕜 L hk xs
    exact (le_sup_left : tensorLowSpan 𝕜 L n ≤ tensorLowSpan 𝕜 L n ⊔ tensorHighSpan 𝕜 L n) hx
  · have hx : TensorAlgebra.tprod 𝕜 L k xs ∈ tensorHighSpan 𝕜 L n :=
      Submodule.subset_span ⟨k, Nat.le_of_not_gt hk, xs, rfl⟩
    exact (le_sup_right : tensorHighSpan 𝕜 L n ≤ tensorLowSpan 𝕜 L n ⊔ tensorHighSpan 𝕜 L n) hx

lemma low_sup_high_eq_top (n : ℕ) :
    tensorLowSpan 𝕜 L n ⊔ tensorHighSpan 𝕜 L n = ⊤ := by
  apply eq_top_iff.2
  rw [← span_allTprods_eq_top 𝕜 L]
  apply Submodule.span_le.2
  intro t ht
  have ht' : t ∈ ⋃ k : ℕ, Set.range (TensorAlgebra.tprod 𝕜 L k) := ht
  obtain ⟨k, htk⟩ := Set.mem_iUnion.mp ht'
  obtain ⟨xs, rfl⟩ := htk
  exact tprod_mem_low_or_high (𝕜 := 𝕜) (L := L) (n := n) xs

lemma low_sup_lengthIdeal_eq_top (n : ℕ) :
    tensorLowSpan 𝕜 L n ⊔ (tensorLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜 = ⊤ := by
  apply le_antisymm le_top
  calc
    (⊤ : Submodule 𝕜 T) = tensorLowSpan 𝕜 L n ⊔ tensorHighSpan 𝕜 L n :=
      (low_sup_high_eq_top 𝕜 L n).symm
    _ ≤ tensorLowSpan 𝕜 L n ⊔ (tensorLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜 :=
      sup_le_sup_left (tensorHighSpan_le_lengthIdeal 𝕜 L n) _

lemma finiteDimensional_tensorLengthQuotient (n : ℕ) :
    FiniteDimensional 𝕜 (T ⧸ (tensorLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜) := by
  let p : Submodule 𝕜 T := (tensorLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜
  let π : T →ₗ[𝕜] T ⧸ p := p.mkQ
  haveI : FiniteDimensional 𝕜 (tensorLowSpan 𝕜 L n) :=
    FiniteDimensional.span_of_finite 𝕜 (shortBasisTprods_finite 𝕜 L n)
  let f : tensorLowSpan 𝕜 L n →ₗ[𝕜] T ⧸ p := π.comp (tensorLowSpan 𝕜 L n).subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p y
    have hx : x ∈ tensorLowSpan 𝕜 L n ⊔ p := by
      rw [low_sup_lengthIdeal_eq_top]
      trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨⟨a, ha⟩, ?_⟩
    change π a = π (a + b)
    have : π b = 0 := (Submodule.Quotient.mk_eq_zero p).2 hb
    simp [this]
  exact FiniteDimensional.of_surjective f hf

/-! ### Length left ideal of `U(L)` -/

def iotaWord (xs : List L) : U :=
  (xs.map (UniversalEnvelopingAlgebra.ι 𝕜)).prod

lemma iotaWord_ofFn {n : ℕ} (xs : Fin n → L) :
    iotaWord 𝕜 L (List.ofFn xs) =
      UniversalEnvelopingAlgebra.mkAlgHom 𝕜 L (TensorAlgebra.tprod 𝕜 L n xs) := by
  simp [iotaWord, TensorAlgebra.tprod_apply, UniversalEnvelopingAlgebra.mkAlgHom,
    map_list_prod, Function.comp_def]

noncomputable def envelopingLengthLeftIdeal (n : ℕ) : Submodule U U :=
  Submodule.span U (Set.range fun xs : Fin n → L => iotaWord 𝕜 L (List.ofFn xs))

lemma mkAlgHom_tprod_mem_enveloping {n : ℕ} (xs : Fin n → L) :
    UniversalEnvelopingAlgebra.mkAlgHom 𝕜 L (TensorAlgebra.tprod 𝕜 L n xs) ∈
      envelopingLengthLeftIdeal 𝕜 L n := by
  rw [← iotaWord_ofFn]
  exact Submodule.subset_span ⟨xs, rfl⟩

lemma mkAlgHom_maps_lengthIdeal (n : ℕ) {t : T}
    (ht : t ∈ tensorLengthLeftIdeal 𝕜 L n) :
    UniversalEnvelopingAlgebra.mkAlgHom 𝕜 L t ∈ envelopingLengthLeftIdeal 𝕜 L n := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨xs, rfl⟩ := hx
      exact mkAlgHom_tprod_mem_enveloping 𝕜 L xs
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
  | smul a x _ hx =>
      rw [smul_eq_mul, map_mul]
      exact Submodule.smul_mem _ _ hx

lemma mkAlgHom_surjective :
    Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom 𝕜 L) :=
  RingCon.mkₐ_surjective (UniversalEnvelopingAlgebra.ringCon 𝕜 L)

noncomputable def tensorToEnvelopingLengthQuotient (n : ℕ) :
    T →ₗ[𝕜] U ⧸ (envelopingLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜 :=
  ((envelopingLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜).mkQ ∘ₗ
    (UniversalEnvelopingAlgebra.mkAlgHom 𝕜 L).toLinearMap

lemma tensorLength_le_ker_tensorToEnveloping (n : ℕ) :
    (tensorLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜 ≤
      LinearMap.ker (tensorToEnvelopingLengthQuotient 𝕜 L n) := by
  intro t ht
  simp only [LinearMap.mem_ker, tensorToEnvelopingLengthQuotient, LinearMap.comp_apply]
  exact (Submodule.Quotient.mk_eq_zero _).2 (mkAlgHom_maps_lengthIdeal 𝕜 L n ht)

lemma finiteDimensional_envelopingLengthQuotient (n : ℕ) :
    FiniteDimensional 𝕜 (U ⧸ (envelopingLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜) := by
  haveI := finiteDimensional_tensorLengthQuotient 𝕜 L n
  let p := (tensorLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜
  let f := tensorToEnvelopingLengthQuotient 𝕜 L n
  let f' : (T ⧸ p) →ₗ[𝕜] U ⧸ (envelopingLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜 :=
    Submodule.liftQ p f (tensorLength_le_ker_tensorToEnveloping 𝕜 L n)
  have hf' : Function.Surjective f' := by
    intro y
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective
      ((envelopingLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜) y
    obtain ⟨t, ht⟩ := mkAlgHom_surjective 𝕜 L u
    refine ⟨p.mkQ t, ?_⟩
    simp [f', f, tensorToEnvelopingLengthQuotient, ht]
  exact FiniteDimensional.of_surjective f' hf'

/-! ### LCS-weighted left ideal -/

noncomputable def nilradicalLCSDepth (x : L)
    (hx : x ∈ LieAlgebra.maxNilpotentIdeal 𝕜 L) : ℕ :=
  let N := LieAlgebra.maxNilpotentIdeal 𝕜 L
  letI : IsNoetherian 𝕜 L := IsNoetherian.iff_fg.2 inferInstance
  (Finset.range (nilpotencyLength L N + 1)).sup fun k =>
    if (⟨x, hx⟩ : N) ∈ lowerCentralSeries 𝕜 L N k then k else 0

noncomputable def lcsAdaptedWeight (i : Fin (basisIndex 𝕜 L)) : ℕ :=
  let x := finBasisL 𝕜 L i
  if hx : x ∈ LieAlgebra.maxNilpotentIdeal 𝕜 L then
    nilradicalLCSDepth 𝕜 L x hx + 1
  else
    1

lemma lcsAdaptedWeight_pos (i : Fin (basisIndex 𝕜 L)) :
    1 ≤ lcsAdaptedWeight 𝕜 L i := by
  by_cases hx : finBasisL 𝕜 L i ∈ LieAlgebra.maxNilpotentIdeal 𝕜 L
  · simp [lcsAdaptedWeight, hx]
  · simp [lcsAdaptedWeight, hx]

noncomputable def basisWordWeight {n : ℕ} (f : Fin n → Fin (basisIndex 𝕜 L)) : ℕ :=
  ∑ i, lcsAdaptedWeight 𝕜 L (f i)

lemma basisWordWeight_ge_length {n : ℕ} (f : Fin n → Fin (basisIndex 𝕜 L)) :
    n ≤ basisWordWeight 𝕜 L f := by
  have h : ∑ _i : Fin n, (1 : ℕ) ≤ ∑ i, lcsAdaptedWeight 𝕜 L (f i) :=
    Finset.sum_le_sum fun i _ => lcsAdaptedWeight_pos 𝕜 L (f i)
  have hcard : ∑ _i : Fin n, (1 : ℕ) = n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_one]
  exact hcard.symm.trans_le (by exact h)

noncomputable def basisIotaWord {n : ℕ} (f : Fin n → Fin (basisIndex 𝕜 L)) : U :=
  iotaWord 𝕜 L (List.ofFn fun i => finBasisL 𝕜 L (f i))

noncomputable def weightedLeftIdeal (N : ℕ) : Submodule U U :=
  Submodule.span U
    {u | ∃ (k : ℕ) (f : Fin k → Fin (basisIndex 𝕜 L)),
      N ≤ basisWordWeight 𝕜 L f ∧ u = basisIotaWord 𝕜 L f}

noncomputable def defaultCutoff : ℕ :=
  ∑ i : Fin (basisIndex 𝕜 L), lcsAdaptedWeight 𝕜 L i + 1

lemma envelopingLengthLeftIdeal_le_weightedLeftIdeal {n : ℕ}
    (hn : defaultCutoff 𝕜 L ≤ n) :
    envelopingLengthLeftIdeal 𝕜 L n ≤ weightedLeftIdeal 𝕜 L (defaultCutoff 𝕜 L) := by
  refine Submodule.span_le.2 ?_
  rintro u ⟨xs, rfl⟩
  change iotaWord 𝕜 L (List.ofFn xs) ∈ weightedLeftIdeal 𝕜 L (defaultCutoff 𝕜 L)
  have hx :
      iotaWord 𝕜 L (List.ofFn xs) =
        UniversalEnvelopingAlgebra.mkAlgHom 𝕜 L (TensorAlgebra.tprod 𝕜 L n xs) :=
    iotaWord_ofFn 𝕜 L xs
  rw [hx, tprod_eq_sum_basis_tprod, map_sum]
  refine sum_mem fun f _ => ?_
  have hw : defaultCutoff 𝕜 L ≤ basisWordWeight 𝕜 L f :=
    le_trans hn (basisWordWeight_ge_length 𝕜 L f)
  have hword :
      UniversalEnvelopingAlgebra.mkAlgHom 𝕜 L
          (TensorAlgebra.tprod 𝕜 L n fun i => finBasisL 𝕜 L (f i)) =
        basisIotaWord 𝕜 L f := by
    rw [← iotaWord_ofFn]
    rfl
  have hgen : basisIotaWord 𝕜 L f ∈ weightedLeftIdeal 𝕜 L (defaultCutoff 𝕜 L) :=
    Submodule.subset_span ⟨n, f, hw, rfl⟩
  rw [map_smul, hword]
  exact (weightedLeftIdeal 𝕜 L (defaultCutoff 𝕜 L)).restrictScalars 𝕜 |>.smul_mem _ hgen

lemma finiteDimensional_weightedQuotient :
    FiniteDimensional 𝕜
      (U ⧸ (weightedLeftIdeal 𝕜 L (defaultCutoff 𝕜 L)).restrictScalars 𝕜) := by
  haveI := finiteDimensional_envelopingLengthQuotient 𝕜 L (defaultCutoff 𝕜 L)
  let p := (envelopingLengthLeftIdeal 𝕜 L (defaultCutoff 𝕜 L)).restrictScalars 𝕜
  let q := (weightedLeftIdeal 𝕜 L (defaultCutoff 𝕜 L)).restrictScalars 𝕜
  have hpq : p ≤ q := envelopingLengthLeftIdeal_le_weightedLeftIdeal 𝕜 L le_rfl
  exact FiniteDimensional.of_surjective (Submodule.factor hpq) (Submodule.factor_surjective hpq)

/-! ### Minimal PBW interface and class-≤-2 length truncation -/

/-- Named remaining Poincaré–Birkhoff–Witt leaf. This is **not** TauCeti ordered spanning. -/
def DegreeOneSurvivesWeightedTruncation : Prop :=
  ∀ x : L, x ≠ 0 →
    UniversalEnvelopingAlgebra.ι 𝕜 x ∉ weightedLeftIdeal 𝕜 L (defaultCutoff 𝕜 L)

lemma twoStep_kills_iotaWord_of_length_ge_three
    (h : LeeAdoNilpotent.IsClassLETwo 𝕜 L) (xs : List L) (hxs : 3 ≤ xs.length) :
    LeeAdoNilpotent.twoStepEnveloping 𝕜 L h (iotaWord 𝕜 L xs) = 0 := by
  obtain ⟨a, b, c, rest, rfl⟩ : ∃ a b c rest, xs = a :: b :: c :: rest := by
    cases xs with
    | nil =>
        have : ¬ (3 ≤ (0 : ℕ)) := by decide
        exact (this hxs).elim
    | cons a xs =>
      cases xs with
      | nil =>
          have : ¬ (3 ≤ (1 : ℕ)) := by decide
          exact (this hxs).elim
      | cons b xs =>
        cases xs with
        | nil =>
            have : ¬ (3 ≤ (2 : ℕ)) := by decide
            exact (this hxs).elim
        | cons c rest => exact ⟨a, b, c, rest, rfl⟩
  have h3 := LeeAdoNilpotent.twoStepEnveloping_ι_mul_three 𝕜 L h a b c
  have hprefix :
      LeeAdoNilpotent.twoStepEnveloping 𝕜 L h (UniversalEnvelopingAlgebra.ι 𝕜 a) *
          LeeAdoNilpotent.twoStepEnveloping 𝕜 L h (UniversalEnvelopingAlgebra.ι 𝕜 b) *
          LeeAdoNilpotent.twoStepEnveloping 𝕜 L h (UniversalEnvelopingAlgebra.ι 𝕜 c) = 0 := by
    simpa [map_mul] using h3
  simp only [iotaWord, List.map_cons, List.prod_cons, map_mul]
  calc
    _ = (LeeAdoNilpotent.twoStepEnveloping 𝕜 L h (UniversalEnvelopingAlgebra.ι 𝕜 a) *
          LeeAdoNilpotent.twoStepEnveloping 𝕜 L h (UniversalEnvelopingAlgebra.ι 𝕜 b) *
          LeeAdoNilpotent.twoStepEnveloping 𝕜 L h (UniversalEnvelopingAlgebra.ι 𝕜 c)) *
          LeeAdoNilpotent.twoStepEnveloping 𝕜 L h
            ((rest.map (UniversalEnvelopingAlgebra.ι 𝕜)).prod) := by
        simp [mul_assoc]
    _ = 0 := by rw [hprefix, zero_mul]

lemma twoStep_kills_envelopingLengthLeftIdeal
    (h : LeeAdoNilpotent.IsClassLETwo 𝕜 L) {n : ℕ} (hn : 3 ≤ n) {u : U}
    (hu : u ∈ envelopingLengthLeftIdeal 𝕜 L n) :
    LeeAdoNilpotent.twoStepEnveloping 𝕜 L h u = 0 := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨xs, rfl⟩ := hy
      refine twoStep_kills_iotaWord_of_length_ge_three 𝕜 L h (List.ofFn xs) ?_
      simpa
  | zero => simp
  | add a b _ _ ha hb =>
      rw [map_add, ha, hb, add_zero]
  | smul a y _ hy =>
      rw [smul_eq_mul, map_mul, hy, mul_zero]

/-- Class ≤ 2: unweighted length-3 truncation already misses the degree-one copy of `L`.
This is the compiled class-2 case of a finite-codimension left ideal missing `ι(L)`. -/
lemma iota_not_mem_envelopingLengthLeftIdeal_of_class_le_two
    (h : LeeAdoNilpotent.IsClassLETwo 𝕜 L) {x : L} (hx : x ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    UniversalEnvelopingAlgebra.ι 𝕜 x ∉ envelopingLengthLeftIdeal 𝕜 L n := by
  intro hmem
  have h0 := twoStep_kills_envelopingLengthLeftIdeal 𝕜 L h hn hmem
  exact LeeAdoNilpotent.iota_not_mem_ker_twoStepEnveloping 𝕜 L h hx h0

/-- Length-3 truncated enveloping quotient is a faithful finite-dimensional `L`-module
whenever `[[L,L],L] = 0`. Unweighted truncation cannot be used for class ≥ 3. -/
lemma existsFaithfulFiniteDimensional_of_class_le_two_lengthTruncation
    (h : LeeAdoNilpotent.IsClassLETwo 𝕜 L) :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule L V) (_ : LieModule 𝕜 L V),
        LieModule.IsFaithful 𝕜 L V := by
  let J := envelopingLengthLeftIdeal 𝕜 L 3
  letI : LieRingModule U (U ⧸ J) := LieRingModule.ofAssociativeModule
  letI : LieModule 𝕜 U (U ⧸ J) := LieModule.ofAssociativeModule
  letI : LieRingModule L (U ⧸ J) :=
    LieRingModule.compLieHom (U ⧸ J) (UniversalEnvelopingAlgebra.ι 𝕜)
  letI : LieModule 𝕜 L (U ⧸ J) :=
    LieModule.compLieHom (U ⧸ J) (UniversalEnvelopingAlgebra.ι 𝕜)
  haveI : FiniteDimensional 𝕜 (U ⧸ (J.restrictScalars 𝕜)) :=
    finiteDimensional_envelopingLengthQuotient 𝕜 L 3
  haveI : FiniteDimensional 𝕜 (U ⧸ J) := this
  refine ⟨U ⧸ J, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine LieModule.IsFaithful.mk ?_
  intro x y hxy
  have hsub : LieModule.toEnd 𝕜 L (U ⧸ J) (x - y) = 0 := by
    have : LieModule.toEnd 𝕜 L (U ⧸ J) x = LieModule.toEnd 𝕜 L (U ⧸ J) y := hxy
    rw [map_sub, this, sub_self]
  have hz1 :
      (LieModule.toEnd 𝕜 L (U ⧸ J) (x - y)) (Submodule.Quotient.mk (1 : U)) = 0 := by
    rw [hsub, LinearMap.zero_apply]
  have hzJ : UniversalEnvelopingAlgebra.ι 𝕜 (x - y) ∈ J := by
    have hact :
        (LieModule.toEnd 𝕜 L (U ⧸ J) (x - y)) (Submodule.Quotient.mk (1 : U)) =
          Submodule.Quotient.mk (UniversalEnvelopingAlgebra.ι 𝕜 (x - y) * (1 : U)) :=
      rfl
    rw [hact, mul_one] at hz1
    exact (Submodule.Quotient.mk_eq_zero J).1 hz1
  apply sub_eq_zero.mp
  by_contra hz0
  exact iota_not_mem_envelopingLengthLeftIdeal_of_class_le_two 𝕜 L h hz0 (n := 3) (by norm_num) hzJ

/-- **Original false statement (h11), retained only as a named proposition.**

The claim
`DegreeOneSurvivesWeightedTruncation` for *arbitrary* finite-dimensional `L`
(all-positive default LCS weights, no nilpotency hypothesis) is false. It is not
the missing half of PBW. See `CONTROLLER_REJECTION.md` and the counterexample
`not_degreeOneSurvives_of_bracket_eq_self` below.

The theorem formerly named `degreeOneSurvivesWeightedTruncation` asserted this
proposition for every `L`. That theorem is deleted; the proposition is kept so
the valid *conditional* packaging
`existsFiniteDimensionalLieModule_of_degreeOneSurvives` still type-checks.
-/

lemma iotaWord_cons (x : L) (xs : List L) :
    iotaWord 𝕜 L (x :: xs) =
      UniversalEnvelopingAlgebra.ι 𝕜 x * iotaWord 𝕜 L xs := by
  simp [iotaWord, List.map_cons, List.prod_cons]

lemma iotaWord_snoc (xs : List L) (x : L) :
    iotaWord 𝕜 L (xs ++ [x]) =
      iotaWord 𝕜 L xs * UniversalEnvelopingAlgebra.ι 𝕜 x := by
  simp [iotaWord, List.map_append, List.prod_append]

lemma iotaWord_ofFn_cons {n : ℕ} (x : L) (xs : Fin n → L) :
    iotaWord 𝕜 L (List.ofFn (Fin.cons x xs)) =
      UniversalEnvelopingAlgebra.ι 𝕜 x * iotaWord 𝕜 L (List.ofFn xs) := by
  simp [iotaWord, List.ofFn_succ, List.map_cons, List.prod_cons]

lemma iotaWord_ofFn_snoc {n : ℕ} (xs : Fin n → L) (x : L) :
    iotaWord 𝕜 L (List.ofFn (Fin.snoc xs x)) =
      iotaWord 𝕜 L (List.ofFn xs) * UniversalEnvelopingAlgebra.ι 𝕜 x := by
  rw [Fin.snoc_eq_append, List.ofFn_fin_append]
  have hx : List.ofFn (Fin.cons x Fin.elim0) = [x] := by
    simp [List.ofFn_succ]
  rw [hx, iotaWord_snoc]

lemma iotaWord_mem_envelopingLengthLeftIdeal {n : ℕ} (xs : Fin n → L) :
    iotaWord 𝕜 L (List.ofFn xs) ∈ envelopingLengthLeftIdeal 𝕜 L n :=
  Submodule.subset_span (Set.mem_range_self xs)

lemma iotaWord_mem_envelopingLengthLeftIdeal_of_le {n k : ℕ} (h : n ≤ k)
    (xs : Fin k → L) :
    iotaWord 𝕜 L (List.ofFn xs) ∈ envelopingLengthLeftIdeal 𝕜 L n := by
  rw [iotaWord_ofFn]
  exact mkAlgHom_maps_lengthIdeal 𝕜 L n (tprod_mem_tensorLengthLeftIdeal_of_le 𝕜 L h xs)

/-- `𝕜`-span of length-`n` generator words. Contained in the length-`n` left ideal. -/
def envelopingLengthSpan (n : ℕ) : Submodule 𝕜 U :=
  Submodule.span 𝕜 (Set.range fun xs : Fin n → L => iotaWord 𝕜 L (List.ofFn xs))

lemma envelopingLengthSpan_le_leftIdeal (n : ℕ) :
    envelopingLengthSpan 𝕜 L n ≤
      (envelopingLengthLeftIdeal 𝕜 L n).restrictScalars 𝕜 :=
  Submodule.span_le.2 fun u hu => by
    obtain ⟨xs, rfl⟩ := Set.mem_range.mp hu
    exact iotaWord_mem_envelopingLengthLeftIdeal 𝕜 L xs

lemma iota_mul_mem_envelopingLengthSpan {n : ℕ} (x : L) {u : U}
    (hu : u ∈ envelopingLengthSpan 𝕜 L n) :
    UniversalEnvelopingAlgebra.ι 𝕜 x * u ∈ envelopingLengthSpan 𝕜 L (n + 1) := by
  refine Submodule.span_induction
    (p := fun v _ => UniversalEnvelopingAlgebra.ι 𝕜 x * v ∈ envelopingLengthSpan 𝕜 L (n + 1))
    ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨xs, rfl⟩
    rw [← iotaWord_ofFn_cons]
    exact Submodule.subset_span ⟨Fin.cons x xs, rfl⟩
  · simp
  · intro a b _ _ ha hb
    rw [mul_add]
    exact add_mem ha hb
  · intro r a _ ha
    rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ r ha

lemma mul_iota_mem_envelopingLengthSpan {n : ℕ} (x : L) {u : U}
    (hu : u ∈ envelopingLengthSpan 𝕜 L n) :
    u * UniversalEnvelopingAlgebra.ι 𝕜 x ∈ envelopingLengthSpan 𝕜 L (n + 1) := by
  refine Submodule.span_induction
    (p := fun v _ => v * UniversalEnvelopingAlgebra.ι 𝕜 x ∈ envelopingLengthSpan 𝕜 L (n + 1))
    ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨xs, rfl⟩
    rw [← iotaWord_ofFn_snoc]
    exact Submodule.subset_span ⟨Fin.snoc xs x, rfl⟩
  · simp
  · intro a b _ _ ha hb
    rw [add_mul]
    exact add_mem ha hb
  · intro r a _ ha
    rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem _ r ha

lemma ad_iota_mem_envelopingLengthSpan {n : ℕ} (h : L) {u : U}
    (hu : u ∈ envelopingLengthSpan 𝕜 L n) :
    UniversalEnvelopingAlgebra.ι 𝕜 h * u - u * UniversalEnvelopingAlgebra.ι 𝕜 h ∈
      envelopingLengthSpan 𝕜 L (n + 1) :=
  sub_mem (iota_mul_mem_envelopingLengthSpan 𝕜 L h hu)
    (mul_iota_mem_envelopingLengthSpan 𝕜 L h hu)

lemma iota_mem_envelopingLengthSpan_one (x : L) :
    UniversalEnvelopingAlgebra.ι 𝕜 x ∈ envelopingLengthSpan 𝕜 L 1 := by
  have hx :
      iotaWord 𝕜 L (List.ofFn fun _ : Fin 1 => x) =
        UniversalEnvelopingAlgebra.ι 𝕜 x := by
    simp [iotaWord, List.ofFn_succ]
  rw [← hx]
  exact Submodule.subset_span (Set.mem_range_self (fun _ : Fin 1 => x))

/-- Iterated enveloping commutator with `ι h` lands in the length-`(n+1)` span. -/
lemma iterate_ad_iota_mem_envelopingLengthSpan (h e : L) (n : ℕ) :
    (fun u : U =>
        UniversalEnvelopingAlgebra.ι 𝕜 h * u -
          u * UniversalEnvelopingAlgebra.ι 𝕜 h)^[n]
      (UniversalEnvelopingAlgebra.ι 𝕜 e) ∈
      envelopingLengthSpan 𝕜 L (n + 1) := by
  induction n with
  | zero =>
      simpa using iota_mem_envelopingLengthSpan_one 𝕜 L e
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ad_iota_mem_envelopingLengthSpan 𝕜 L h ih

lemma iterate_ad_iota_eq_of_bracket_eq_self
    {h e : L} (hbr : ⁅h, e⁆ = e) (n : ℕ) :
    (fun u : U =>
        UniversalEnvelopingAlgebra.ι 𝕜 h * u -
          u * UniversalEnvelopingAlgebra.ι 𝕜 h)^[n]
      (UniversalEnvelopingAlgebra.ι 𝕜 e) =
      UniversalEnvelopingAlgebra.ι 𝕜 e := by
  have had :
      UniversalEnvelopingAlgebra.ι 𝕜 h * UniversalEnvelopingAlgebra.ι 𝕜 e -
          UniversalEnvelopingAlgebra.ι 𝕜 e * UniversalEnvelopingAlgebra.ι 𝕜 h =
        UniversalEnvelopingAlgebra.ι 𝕜 e := by
    have hlie :
        ⁅UniversalEnvelopingAlgebra.ι 𝕜 h, UniversalEnvelopingAlgebra.ι 𝕜 e⁆ =
          UniversalEnvelopingAlgebra.ι 𝕜 e := by
      simpa [hbr] using
        (LieHom.map_lie (UniversalEnvelopingAlgebra.ι 𝕜 (L := L)) h e).symm
    simpa [LieRing.of_associative_ring_bracket] using hlie
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, had]

/-- If `[h,e] = e` with `e ≠ 0`, then `ι(e)` already lies in every positive-length
left ideal, hence in the default all-positive weighted ideal. This is the
controller's `[h,e]=e` obstruction: the old universal degree-one survival is
false independently of PBW. -/
lemma not_degreeOneSurvives_of_bracket_eq_self
    {h e : L} (he : e ≠ 0) (hbr : ⁅h, e⁆ = e) :
    ¬ DegreeOneSurvivesWeightedTruncation (𝕜 := 𝕜) (L := L) := by
  intro hsurv
  have hcut : 1 ≤ defaultCutoff 𝕜 L := Nat.succ_le_succ (Nat.zero_le _)
  let n : ℕ := defaultCutoff 𝕜 L - 1
  have hn : n + 1 = defaultCutoff 𝕜 L := Nat.sub_add_cancel hcut
  have hspan :
      UniversalEnvelopingAlgebra.ι 𝕜 e ∈ envelopingLengthSpan 𝕜 L (n + 1) := by
    have hiter := iterate_ad_iota_mem_envelopingLengthSpan 𝕜 L h e n
    rwa [iterate_ad_iota_eq_of_bracket_eq_self (𝕜 := 𝕜) (L := L) hbr n] at hiter
  have hmem :
      UniversalEnvelopingAlgebra.ι 𝕜 e ∈ envelopingLengthLeftIdeal 𝕜 L (n + 1) :=
    envelopingLengthSpan_le_leftIdeal 𝕜 L (n + 1) hspan
  have hle :
      envelopingLengthLeftIdeal 𝕜 L (n + 1) ≤
        weightedLeftIdeal 𝕜 L (defaultCutoff 𝕜 L) := by
    simpa [hn] using
      envelopingLengthLeftIdeal_le_weightedLeftIdeal (𝕜 := 𝕜) (L := L)
        (n := n + 1) le_rfl
  exact hsurv e he (hle hmem)

/-- Concrete affine pair in `gl(2)`: `h = E₀₀`, `e = E₀₁` satisfy `[h,e] = e`. -/
lemma gl2_exists_bracket_eq_self :
    ∃ (h e : Matrix (Fin 2) (Fin 2) 𝕜), e ≠ 0 ∧ ⁅h, e⁆ = e := by
  let hM : Matrix (Fin 2) (Fin 2) 𝕜 := Matrix.single 0 0 1
  let eM : Matrix (Fin 2) (Fin 2) 𝕜 := Matrix.single 0 1 1
  refine ⟨hM, eM, ?_, ?_⟩
  · intro h0
    have : (eM 0 1 : 𝕜) = 0 := by simp [h0]
    simp [eM] at this
  · change hM * eM - eM * hM = eM
    have hmul : hM * eM = eM := by
      simpa [hM, eM, one_mul] using
        (Matrix.single_mul_single_same (i := (0 : Fin 2)) (j := (0 : Fin 2))
          (k := (1 : Fin 2)) (c := (1 : 𝕜)) (1 : 𝕜))
    have hmul' : eM * hM = 0 := by
      simpa [hM, eM] using
        (Matrix.single_mul_single_of_ne (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (k := (0 : Fin 2)) (c := (1 : 𝕜)) Fin.zero_ne_one.symm (1 : 𝕜))
    simp [hmul, hmul']

/-- The old all-`L` default positive-weight truncation theorem is false already
on `gl(2)`. -/
theorem not_degreeOneSurvivesWeightedTruncation_gl2 :
    ¬ DegreeOneSurvivesWeightedTruncation
        (𝕜 := 𝕜) (L := Matrix (Fin 2) (Fin 2) 𝕜) := by
  obtain ⟨h, e, he, hbr⟩ := gl2_exists_bracket_eq_self (𝕜 := 𝕜)
  exact not_degreeOneSurvives_of_bracket_eq_self (𝕜 := 𝕜)
    (L := Matrix (Fin 2) (Fin 2) 𝕜) he hbr

lemma existsFiniteDimensionalLieModule_of_degreeOneSurvives
    (h : DegreeOneSurvivesWeightedTruncation (𝕜 := 𝕜) (L := L)) :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule L V) (_ : LieModule 𝕜 L V),
        LieModule.IsFaithful 𝕜 L V := by
  let J := weightedLeftIdeal 𝕜 L (defaultCutoff 𝕜 L)
  letI : LieRingModule U (U ⧸ J) := LieRingModule.ofAssociativeModule
  letI : LieModule 𝕜 U (U ⧸ J) := LieModule.ofAssociativeModule
  letI : LieRingModule L (U ⧸ J) :=
    LieRingModule.compLieHom (U ⧸ J) (UniversalEnvelopingAlgebra.ι 𝕜)
  letI : LieModule 𝕜 L (U ⧸ J) :=
    LieModule.compLieHom (U ⧸ J) (UniversalEnvelopingAlgebra.ι 𝕜)
  haveI : FiniteDimensional 𝕜 (U ⧸ (J.restrictScalars 𝕜)) :=
    finiteDimensional_weightedQuotient 𝕜 L
  haveI : FiniteDimensional 𝕜 (U ⧸ J) := this
  refine ⟨U ⧸ J, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine LieModule.IsFaithful.mk ?_
  intro x y hxy
  have hsub : LieModule.toEnd 𝕜 L (U ⧸ J) (x - y) = 0 := by
    have : LieModule.toEnd 𝕜 L (U ⧸ J) x = LieModule.toEnd 𝕜 L (U ⧸ J) y := hxy
    rw [map_sub, this, sub_self]
  have hz1 :
      (LieModule.toEnd 𝕜 L (U ⧸ J) (x - y)) (Submodule.Quotient.mk (1 : U)) = 0 := by
    rw [hsub, LinearMap.zero_apply]
  have hzJ : UniversalEnvelopingAlgebra.ι 𝕜 (x - y) ∈ J := by
    have hact :
        (LieModule.toEnd 𝕜 L (U ⧸ J) (x - y)) (Submodule.Quotient.mk (1 : U)) =
          Submodule.Quotient.mk (UniversalEnvelopingAlgebra.ι 𝕜 (x - y) * (1 : U)) :=
      rfl
    rw [hact, mul_one] at hz1
    exact (Submodule.Quotient.mk_eq_zero J).1 hz1
  apply sub_eq_zero.mp
  by_contra hz0
  exact h (x - y) hz0 hzJ

end LeeAdoWeightedTruncation
