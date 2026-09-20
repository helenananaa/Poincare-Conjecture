import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Linear algebra for the regular-preimage theorem at a boundary point

For the standard half-space model in `EuclideanSpace ℝ (Fin (n + 1))`, coordinate `0` is the
normal coordinate.  Its kernel is therefore the tangent hyperplane of the boundary.  This file
records the elementary linear step used in Problem 5-23: if `A` is onto after restriction to that
hyperplane, then the joint map `v ↦ (A v, v 0)` is onto.
-/

noncomputable section

namespace Manifold

/-- The normal-coordinate functional for the standard `(n + 1)`-dimensional half-space. -/
def standardHalfSpaceNormal (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
  EuclideanSpace.proj (i := (0 : Fin (n + 1)))

/-- The intrinsic tangent model of the boundary of the standard half-space. -/
abbrev StandardBoundaryTangent (n : ℕ) := (standardHalfSpaceNormal n).ker

/-- Restrict a continuous linear map to the tangent hyperplane of the standard half-space. -/
def restrictToStandardBoundaryTangent {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    StandardBoundaryTangent n →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  A.comp (standardHalfSpaceNormal n).ker.subtypeL

/-- Surjectivity in every tangential direction makes the joint map `(A, normal)` surjective. -/
theorem surjective_prod_standardHalfSpaceNormal_of_restrict_surjective {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective (restrictToStandardBoundaryTangent A)) :
    Function.Surjective (A.prod (standardHalfSpaceNormal n)) := by
  rintro ⟨y, s⟩
  let normalVector : EuclideanSpace ℝ (Fin (n + 1)) :=
    s • EuclideanSpace.single (0 : Fin (n + 1)) 1
  obtain ⟨w, hw⟩ := hA (y - A normalVector)
  refine ⟨w.1 + normalVector, ?_⟩
  apply Prod.ext
  · change A (w.1 + normalVector) = y
    rw [map_add]
    change A w.1 = y - A normalVector at hw
    rw [hw]
    abel
  · change standardHalfSpaceNormal n (w.1 + normalVector) = s
    rw [map_add]
    have hwNormal : standardHalfSpaceNormal n w.1 = 0 := w.2
    rw [hwNormal, zero_add]
    simp [standardHalfSpaceNormal, normalVector]

/-- Rank coordinates for a continuous linear map of Euclidean spaces: after linear changes of
source and target, the map is the model projection onto the first `r` coordinates. -/
theorem exists_rank_coordinates {m n r : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrank : Module.finrank ℝ A.range = r) :
    ∃ (hrm : r ≤ m) (hrn : r ≤ n),
      ∃ d : EuclideanSpace ℝ (Fin m) ≃L[ℝ]
          (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (m - r))),
        ∃ c : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
          (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (n - r))),
          ∀ x, c (A x) = ((d x).1, 0) := by
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin m)) := A.ker
  let H : Submodule ℝ (EuclideanSpace ℝ (Fin m)) := Kᗮ
  let R : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := A.range
  let C : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Rᗮ
  have hnull := A.toLinearMap.finrank_range_add_finrank_ker
  have hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp
  rw [hrank, hm] at hnull
  have hrm : r ≤ m := by omega
  have hrn : r ≤ n := by
    rw [← hrank]
    simpa using (Submodule.finrank_le (A.range))
  have hfinK : Module.finrank ℝ K = m - r := by
    simp only [K]
    omega
  have hfinH : Module.finrank ℝ H = r := by
    have horth := K.finrank_add_finrank_orthogonal
    simp only [H]
    rw [hfinK] at horth
    rw [hm] at horth
    omega
  have hfinC : Module.finrank ℝ C = n - r := by
    have horth := R.finrank_add_finrank_orthogonal
    simp only [C]
    have hfinR : Module.finrank ℝ R = r := hrank
    rw [hfinR] at horth
    have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
    rw [hn] at horth
    omega
  let eH : H ≃L[ℝ] EuclideanSpace ℝ (Fin r) :=
    ContinuousLinearEquiv.ofFinrankEq (hfinH.trans (by simp))
  let eK : K ≃L[ℝ] EuclideanSpace ℝ (Fin (m - r)) :=
    ContinuousLinearEquiv.ofFinrankEq (hfinK.trans (by simp))
  let eC : C ≃L[ℝ] EuclideanSpace ℝ (Fin (n - r)) :=
    ContinuousLinearEquiv.ofFinrankEq (hfinC.trans (by simp))
  let AH : H →ₗ[ℝ] R :=
    (A.toLinearMap.comp H.subtype).codRestrict R (fun x ↦ A.mem_range_self x)
  have hAHinj : Function.Injective AH := by
    intro x y hxy
    apply Subtype.ext
    have hker : ((x : EuclideanSpace ℝ (Fin m)) - y) ∈ K := by
      change A ((x : EuclideanSpace ℝ (Fin m)) - y) = 0
      have hval : A (x : EuclideanSpace ℝ (Fin m)) = A y := by
        simpa [AH] using congrArg Subtype.val hxy
      simpa only [map_sub] using sub_eq_zero.mpr hval
    have horth : ((x : EuclideanSpace ℝ (Fin m)) - y) ∈ H := H.sub_mem x.property y.property
    have hv : ((x : EuclideanSpace ℝ (Fin m)) - y) ∈ K ⊓ H := ⟨hker, horth⟩
    rw [K.isCompl_orthogonal.inf_eq_bot] at hv
    have : ((x : EuclideanSpace ℝ (Fin m)) - y) = 0 := by simpa using hv
    exact sub_eq_zero.mp this
  have hAHsurj : Function.Surjective AH := by
    intro z
    rcases z.property with ⟨x, hx⟩
    let xHK : H × K :=
      (Submodule.prodEquivOfIsTopCompl H K K.isTopCompl_orthogonal.symm).symm x
    refine ⟨xHK.1, ?_⟩
    apply Subtype.ext
    have hxsplit : (xHK.1 : EuclideanSpace ℝ (Fin m)) + xHK.2 = x :=
      (Submodule.prodEquivOfIsTopCompl H K K.isTopCompl_orthogonal.symm).apply_symm_apply x
    change A (xHK.1 : EuclideanSpace ℝ (Fin m)) = z
    rw [← hx, ← hxsplit]
    simp [K]
  let eHR : H ≃L[ℝ] R :=
    (LinearEquiv.ofBijective AH ⟨hAHinj, hAHsurj⟩).toContinuousLinearEquiv
  let eR : R ≃L[ℝ] EuclideanSpace ℝ (Fin r) := eHR.symm.trans eH
  let splitM : (H × K) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    Submodule.prodEquivOfIsTopCompl H K K.isTopCompl_orthogonal.symm
  let splitN : (R × C) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Submodule.prodEquivOfIsTopCompl R C R.isTopCompl_orthogonal
  let d : EuclideanSpace ℝ (Fin m) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (m - r))) :=
    splitM.symm.trans (eH.prodCongr eK)
  let c : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (n - r))) :=
    splitN.symm.trans (eR.prodCongr eC)
  refine ⟨hrm, hrn, d, c, ?_⟩
  intro x
  let hk : H × K := splitM.symm x
  have hxsplit : (hk.1 : EuclideanSpace ℝ (Fin m)) + hk.2 = x :=
    splitM.apply_symm_apply x
  have hAx : A x = A (hk.1 : EuclideanSpace ℝ (Fin m)) := by
    rw [← hxsplit]
    simp [K]
  let z : R := ⟨A x, A.mem_range_self x⟩
  have hsplitM : splitM.symm x = hk := rfl
  have hsplitN : splitN.symm (A x) = (z, 0) := by
    have hz := Submodule.prodEquivOfIsCompl_symm_apply_left
      R C R.isCompl_orthogonal z
    simpa [splitN, z] using hz
  have hAHz : AH hk.1 = z := by
    apply Subtype.ext
    simpa [AH, z] using hAx.symm
  have heHR : eHR hk.1 = z := by
    simpa [eHR] using hAHz
  have heR : eR z = eH hk.1 := by
    change eH (eHR.symm z) = eH hk.1
    rw [← heHR, eHR.symm_apply_apply]
  change (eR (splitN.symm (A x)).1, eC (splitN.symm (A x)).2) =
    ((eH (splitM.symm x).1, eK (splitM.symm x).2).1, 0)
  rw [hsplitN, hsplitM]
  simpa [heR]

/-- Identify `ℝ` with one-dimensional Euclidean space. -/
def euclideanFinOneEquiv : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.equivOfInverse
    (EuclideanSpace.proj (0 : Fin 1))
    ((1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single (0 : Fin 1) 1))
    (by
      intro x
      ext i
      fin_cases i
      simp)
    (by
      intro s
      simp)

/-- Pack a scalar together with `k` Euclidean coordinates into `ℝ^{k+1}`, putting the scalar in
slot `0`. -/
def packFreeCoordinates (k : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin k)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  (euclideanFinOneEquiv.symm.prodCongr (ContinuousLinearEquiv.refl ℝ
      (EuclideanSpace ℝ (Fin k)))).trans <|
    EuclideanSpace.finAddEquivProd.symm.trans <|
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (Fin.castOrderIso (Nat.add_comm 1 k)).toEquiv).toContinuousLinearEquiv

theorem packFreeCoordinates_apply_zero (k : ℕ) (t : ℝ) (w : EuclideanSpace ℝ (Fin k)) :
    packFreeCoordinates k (t, w) 0 = t := by
  have hcast : ((Fin.castOrderIso (Nat.add_comm 1 k)).toEquiv.symm 0 : Fin (1 + k)) = 0 := by
    apply Fin.ext
    simp
  change
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (Fin.castOrderIso (Nat.add_comm 1 k)).toEquiv)
      (EuclideanSpace.finAddEquivProd.symm
        (euclideanFinOneEquiv.symm t, w)) 0 = t
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  change
      (EuclideanSpace.finAddEquivProd.symm
        (euclideanFinOneEquiv.symm t, w))
        ((Fin.castOrderIso (Nat.add_comm 1 k)).toEquiv.symm 0) = t
  rw [hcast]
  have h0 : (0 : Fin (1 + k)) = Fin.castAdd k (0 : Fin 1) := by
    apply Fin.ext
    simp
  simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd, euclideanFinOneEquiv, h0,
    finSumFinEquiv_symm_apply_castAdd]

theorem packFreeCoordinates_symm_zero (k : ℕ) (u : EuclideanSpace ℝ (Fin (k + 1))) :
    ((packFreeCoordinates k).symm u).1 = u 0 := by
  have h := packFreeCoordinates_apply_zero k
    ((packFreeCoordinates k).symm u).1
    ((packFreeCoordinates k).symm u).2
  simpa using h.symm

/-- A normal-preserving linear identification `ℝ^{k+1} × ℝ^m ≃ ℝ^{n+1}` built from surjectivity of
`A` on `ker dt`.  The first free coordinate is exactly the ambient normal, and `A ∘ L` is the
projection onto the complementary factor. -/
theorem exists_normal_preserving_split {n m : ℕ} (hmn : m ≤ n)
    (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective (restrictToStandardBoundaryTangent A)) :
    ∃ L : (EuclideanSpace ℝ (Fin ((n - m) + 1)) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)),
      (∀ u v, (L (u, v)) 0 = u 0) ∧
        (∀ w, A (L w) = w.2) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let J : E →L[ℝ] (EuclideanSpace ℝ (Fin m) × ℝ) :=
    A.prod (standardHalfSpaceNormal n)
  have hJ : Function.Surjective J :=
    surjective_prod_standardHalfSpaceNormal_of_restrict_surjective A hA
  let K : Submodule ℝ E := J.ker
  have hnull := J.toLinearMap.finrank_range_add_finrank_ker
  have hE : Module.finrank ℝ E = n + 1 := by simp [E]
  have hJtop : LinearMap.range J.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hJ
  have hJrank : Module.finrank ℝ (LinearMap.range J.toLinearMap) = m + 1 := by
    rw [hJtop, finrank_top]
    simp
  have hfinK : Module.finrank ℝ K = n - m := by
    simp only [K]
    have : Module.finrank ℝ (LinearMap.range J.toLinearMap) +
        Module.finrank ℝ J.toLinearMap.ker = n + 1 := by
      simpa [hE] using hnull
    rw [hJrank] at this
    omega
  let eK : K ≃L[ℝ] EuclideanSpace ℝ (Fin (n - m)) :=
    ContinuousLinearEquiv.ofFinrankEq (hfinK.trans (by simp))
  let ψ : E →L[ℝ]
      (ℝ × EuclideanSpace ℝ (Fin (n - m))) × EuclideanSpace ℝ (Fin m) :=
    ((standardHalfSpaceNormal n).prod
      (eK.toContinuousLinearMap.comp K.orthogonalProjectionOnto)).prod A
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hψ : ψ (x - y) = 0 := by
      simpa [map_sub] using congrArg (fun z ↦ z - ψ y) hxy
    have hx0 : standardHalfSpaceNormal n (x - y) = 0 := by
      simpa [ψ] using congrArg (fun z ↦ z.1.1) hψ
    have hK : K.orthogonalProjectionOnto (x - y) = 0 := by
      have hcoord : eK (K.orthogonalProjectionOnto (x - y)) = 0 := by
        simpa [ψ] using congrArg (fun z ↦ z.1.2) hψ
      exact (eK.map_eq_zero_iff).mp hcoord
    have hAxy : A (x - y) = 0 := by
      simpa [ψ] using congrArg (fun z ↦ z.2) hψ
    have hJxy : J (x - y) = 0 := by
      apply Prod.ext
      · simpa [J] using hAxy
      · simpa [J] using hx0
    have hmemK : x - y ∈ K := hJxy
    have hproj : K.orthogonalProjectionOnto (x - y) = ⟨x - y, hmemK⟩ :=
      K.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x - y, hmemK⟩
    have : (⟨x - y, hmemK⟩ : K) = 0 := by
      simpa [hproj] using hK
    exact Subtype.ext_iff.mp this
  have hψfin :
      Module.finrank ℝ
        ((ℝ × EuclideanSpace ℝ (Fin (n - m))) × EuclideanSpace ℝ (Fin m)) = n + 1 := by
    have : 1 + (n - m) + m = n + 1 := by omega
    simp [this]
  have hψsurj : Function.Surjective ψ := by
    have hdim : Module.finrank ℝ E =
        Module.finrank ℝ
          ((ℝ × EuclideanSpace ℝ (Fin (n - m))) × EuclideanSpace ℝ (Fin m)) := by
      simp [hE, hψfin]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hψinj
  let eψ : E ≃L[ℝ]
      (ℝ × EuclideanSpace ℝ (Fin (n - m))) × EuclideanSpace ℝ (Fin m) :=
    (LinearEquiv.ofBijective ψ.toLinearMap ⟨hψinj, hψsurj⟩).toContinuousLinearEquiv
  have heψ : ∀ z, eψ z = ψ z := fun _ ↦ rfl
  let pack :
      (EuclideanSpace ℝ (Fin ((n - m) + 1)) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
        (ℝ × EuclideanSpace ℝ (Fin (n - m))) × EuclideanSpace ℝ (Fin m) :=
    (packFreeCoordinates (n - m)).symm.prodCongr (ContinuousLinearEquiv.refl ℝ _)
  let L :
      (EuclideanSpace ℝ (Fin ((n - m) + 1)) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] E :=
    pack.trans eψ.symm
  refine ⟨L, ?_, ?_⟩
  · intro u v
    have hz : ψ (L (u, v)) = pack (u, v) := by
      change ψ (eψ.symm (pack (u, v))) = pack (u, v)
      rw [← heψ]
      exact eψ.apply_symm_apply _
    have ht : standardHalfSpaceNormal n (L (u, v)) =
        ((packFreeCoordinates (n - m)).symm u).1 := by
      simpa [ψ, pack] using congrArg (fun z ↦ z.1.1) hz
    simpa [standardHalfSpaceNormal, packFreeCoordinates_symm_zero] using ht
  · intro w
    have hz : ψ (L w) = pack w := by
      change ψ (eψ.symm (pack w)) = pack w
      rw [← heψ]
      exact eψ.apply_symm_apply _
    have hA : A (L w) = (pack w).2 := by
      simpa [ψ] using congrArg Prod.snd hz
    simpa [pack] using hA

/-- Concatenate free half-space coordinates with complementary coordinates. -/
def standardConcatEquiv (n m : ℕ) (hmn : m ≤ n) :
    (EuclideanSpace ℝ (Fin ((n - m) + 1)) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  EuclideanSpace.finAddEquivProd.symm.trans <|
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Fin.castOrderIso (by omega : ((n - m) + 1) + m = n + 1)).toEquiv).toContinuousLinearEquiv

theorem standardConcatEquiv_apply_zero (n m : ℕ) (hmn : m ≤ n)
    (u : EuclideanSpace ℝ (Fin ((n - m) + 1))) (v : EuclideanSpace ℝ (Fin m)) :
    standardConcatEquiv n m hmn (u, v) 0 = u 0 := by
  have hcast :
      ((Fin.castOrderIso (by omega : ((n - m) + 1) + m = n + 1)).toEquiv.symm
        0 : Fin (((n - m) + 1) + m)) = 0 := by
    apply Fin.ext
    simp
  have h0 : (0 : Fin (((n - m) + 1) + m)) =
      Fin.castAdd m (0 : Fin ((n - m) + 1)) := by
    apply Fin.ext
    simp
  simp [standardConcatEquiv, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
    hcast, h0, finSumFinEquiv_symm_apply_castAdd]

end Manifold
