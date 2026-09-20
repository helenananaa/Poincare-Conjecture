import Mathlib
import LeeSmoothLib.Ch04.Sec04_21.Exercise_4_4
import LeeSmoothLib.Ch04.Sec04_21.ImmersionDerivative
import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch04.Sec04_25.Proposition_4_28
-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool unavailable in this environment; local precedents used:
-- `Manifold.HasConstantRank`, `Theorem_4_5`, and nearby manifold Euclidean-space item files.

noncomputable section

open Set
open scoped ContDiff Manifold InnerProductSpace

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

universe uM uN

section RankTheorem

variable {m n r : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- The Euclidean normal form for a rank-`r` map keeps the first `r` source coordinates and sends
all remaining target coordinates to `0`. -/
def rank_normal_form (m n r : ℕ) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) :=
  fun x ↦
    WithLp.toLp 2 <| fun i : Fin n ↦
        if i.1 < r then
          if hmi : i.1 < m then
            x ⟨i.1, hmi⟩
          else
            0
        else
          0

/-- On a target coordinate with index `< r` and `< m`, `rank_normal_form` returns the matching
source coordinate. -/
-- Proof sketch: unfold `rank_normal_form` and evaluate the nested `if` expressions using the two
-- index inequalities.
theorem rank_normal_form_apply_of_lt {i : Fin n} (hri : i.1 < r) (hmi : i.1 < m)
    (x : EuclideanSpace ℝ (Fin m)) :
    rank_normal_form m n r x i = x ⟨i.1, hmi⟩ := by
  simp [rank_normal_form, hri, hmi]

/-- A local coordinate normal form for `F` at `p` consists of centered smooth charts on the source
and target in which the coordinate representative of `F` agrees with a prescribed Euclidean model
map. -/
structure LocalCoordinateNormalFormAt (F : M → N) (p : M)
    (normalForm : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) where
  domChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m))
  codChart : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n))
  domChart_mem_maximalAtlas :
    domChart ∈ IsManifold.maximalAtlas I_m ∞ M
  codChart_mem_maximalAtlas :
    codChart ∈ IsManifold.maximalAtlas I_n ∞ N
  domChart_centered : p ∈ domChart.source ∧ domChart p = 0
  codChart_centered : F p ∈ codChart.source ∧ codChart (F p) = 0
  mapsTo : MapsTo F domChart.source codChart.source
  eqOn : EqOn (codChart ∘ F ∘ domChart.symm) normalForm domChart.target

namespace LocalCoordinateNormalFormAt

/-- Any local coordinate normal form carries the source chart domain into the target chart
domain. -/
-- Proof sketch: this is exactly the `mapsTo` field of the structure.
theorem mapsTo_source {F : M → N} {p : M}
    {normalForm : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (h : LocalCoordinateNormalFormAt F p normalForm) :
    MapsTo F h.domChart.source h.codChart.source :=
  h.mapsTo

end LocalCoordinateNormalFormAt

end RankTheorem

private def finSplit {r m : ℕ} (h : r ≤ m) :
    EuclideanSpace ℝ (Fin m) ≃L[ℝ]
      EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (m - r)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Fin.castOrderIso (Nat.add_sub_of_le h).symm).toEquiv).toContinuousLinearEquiv.trans
    EuclideanSpace.finAddEquivProd

private lemma finSplit_rank_normal_form {m n r : ℕ}
    (hrm : r ≤ m) (hrn : r ≤ n) (x : EuclideanSpace ℝ (Fin m)) :
    finSplit hrn (rank_normal_form m n r x) = ((finSplit hrm x).1, 0) := by
  apply Prod.ext
  · ext i
    have hi : (i : ℕ) < m := lt_of_lt_of_le i.isLt hrm
    have hind : (⟨(i : ℕ), hi⟩ : Fin m) =
        Fin.cast (Nat.add_sub_of_le hrm) (Fin.castAdd (m - r) i) := by
      apply Fin.ext
      simp
    simp [finSplit, rank_normal_form, hi, hind]
  · ext i
    simp [finSplit, rank_normal_form, hrm, hrn]

private theorem exists_rank_coordinates {m n r : ℕ}
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
  have hrm : r ≤ m := by
    omega
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
    have hxsplit : (xHK.1 : EuclideanSpace ℝ (Fin m)) + xHK.2 = x := by
      exact (Submodule.prodEquivOfIsTopCompl H K K.isTopCompl_orthogonal.symm).apply_symm_apply x
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
  have hxsplit : (hk.1 : EuclideanSpace ℝ (Fin m)) + hk.2 = x := by
    exact splitM.apply_symm_apply x
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

private lemma tail_eq_zero_of_finrank_range_eq
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (L : (X × Y) →L[ℝ] (X × Z))
    (hhead : ∀ w, (L w).1 = w.1)
    (hrank : Module.finrank ℝ L.range = Module.finrank ℝ X) :
    ∀ y, (L (0, y)).2 = 0 := by
  let P : L.range →ₗ[ℝ] X := (LinearMap.fst ℝ X Z).comp L.range.subtype
  have hPsurj : Function.Surjective P := by
    intro x
    let w : L.range := ⟨L (x, 0), ⟨(x, 0), rfl⟩⟩
    refine ⟨w, ?_⟩
    exact hhead (x, 0)
  have hker : P.ker = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hnull := P.finrank_range_add_finrank_ker
    have hrange : Module.finrank ℝ P.range = Module.finrank ℝ X := by
      rw [LinearMap.range_eq_top.mpr hPsurj, finrank_top]
    rw [hrange, hrank] at hnull
    omega
  intro y
  let w : L.range := ⟨L (0, y), ⟨(0, y), rfl⟩⟩
  have hwker : w ∈ P.ker := by
    change (L (0, y)).1 = 0
    simpa using hhead (0, y)
  rw [hker] at hwker
  have hwzero : (w : X × Z) = 0 := by simpa using hwker
  exact congrArg Prod.snd hwzero

private lemma tail_independent_on_product
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {k : (X × Y) → (X × Z)} {sx : Set X} {sy : Set Y}
    (hxsopen : IsOpen sx) (hsyopen : IsOpen sy)
    (hconv : Convex ℝ sy) (hzero : (0 : Y) ∈ sy)
    (hk : DifferentiableOn ℝ k (sx ×ˢ sy))
    (hhead : Set.EqOn (fun w ↦ (k w).1) Prod.fst (sx ×ˢ sy))
    (hrank : ∀ w ∈ sx ×ˢ sy,
      Module.finrank ℝ (fderiv ℝ k w).range = Module.finrank ℝ X) :
    ∀ x ∈ sx, ∀ y ∈ sy, (k (x, y)).2 = (k (x, 0)).2 := by
  intro x hx y hy
  have hopen : IsOpen (sx ×ˢ sy) := hxsopen.prod hsyopen
  let q : Y → Z := fun t ↦ (k (x, t)).2
  have hqdiff : DifferentiableOn ℝ q sy := by
    intro t ht
    have hkt : DifferentiableAt ℝ k (x, t) :=
      (hk (x, t) ⟨hx, ht⟩).differentiableAt (hopen.mem_nhds ⟨hx, ht⟩)
    exact (hkt.hasFDerivAt.comp t (hasFDerivAt_prodMk_right x t)).snd.differentiableAt
      |>.differentiableWithinAt
  have hqzero : ∀ t ∈ sy, fderivWithin ℝ q sy t = 0 := by
    intro t ht
    have hkt : DifferentiableAt ℝ k (x, t) :=
      (hk (x, t) ⟨hx, ht⟩).differentiableAt (hopen.mem_nhds ⟨hx, ht⟩)
    let L := fderiv ℝ k (x, t)
    have hlocal : (fun w : X × Y ↦ (k w).1) =ᶠ[nhds (x, t)] Prod.fst := by
      filter_upwards [hopen.mem_nhds ⟨hx, ht⟩] with w hw
      exact hhead hw
    have hheadDeriv : (ContinuousLinearMap.fst ℝ X Z).comp L =
        ContinuousLinearMap.fst ℝ X Y := by
      have hleft := hasFDerivAt_fst.comp (x, t) hkt.hasFDerivAt
      have hright : HasFDerivAt (fun w : X × Y ↦ (k w).1)
          (ContinuousLinearMap.fst ℝ X Y) (x, t) :=
        hasFDerivAt_fst.congr_of_eventuallyEq hlocal
      exact hleft.unique hright
    have hheadL : ∀ w, (L w).1 = w.1 := by
      intro w
      exact DFunLike.congr_fun hheadDeriv w
    have htailL : ∀ v, (L (0, v)).2 = 0 :=
      tail_eq_zero_of_finrank_range_eq L hheadL (hrank (x, t) ⟨hx, ht⟩)
    have hslice : HasFDerivAt q (0 : Y →L[ℝ] Z) t := by
      have hderiv := (hkt.hasFDerivAt.comp t (hasFDerivAt_prodMk_right x t)).snd
      have hderiv' : HasFDerivAt q
          ((ContinuousLinearMap.snd ℝ X Z).comp
            (L.comp (ContinuousLinearMap.inr ℝ X Y))) t := by
        simpa [q, L] using hderiv
      convert hderiv' using 1
      ext v
      simpa using (htailL v).symm
    exact (fderivWithin_of_mem_nhds (hsyopen.mem_nhds ht)).trans hslice.fderiv
  exact hconv.is_const_of_fderivWithin_eq_zero hqdiff hqzero hy hzero

private lemma finrank_range_comp_isInvertible_left
    {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : V →L[ℝ] W) (A : U →L[ℝ] V) (hB : B.IsInvertible) :
    Module.finrank ℝ (B.comp A).range = Module.finrank ℝ A.range := by
  rcases hB with ⟨e, rfl⟩
  change Module.finrank ℝ (e.toLinearMap.comp A.toLinearMap).range =
    Module.finrank ℝ A.toLinearMap.range
  rw [LinearMap.range_comp]
  exact e.toLinearEquiv.finrank_map_eq A.range

private lemma finrank_range_comp_isInvertible_right
    {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : V →L[ℝ] W) (A : U →L[ℝ] V) (hA : A.IsInvertible) :
    Module.finrank ℝ (B.comp A).range = Module.finrank ℝ B.range := by
  rcases hA with ⟨e, rfl⟩
  change Module.finrank ℝ (B.toLinearMap.comp e.toLinearMap).range =
    Module.finrank ℝ B.toLinearMap.range
  rw [LinearMap.range_comp_of_range_eq_top B.toLinearMap e.toLinearEquiv.range]

private def preferredChartPartialDiffeomorph
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    (x : M) : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

private def PartialDiffeomorph.restrOpen
    {E F H G M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    (e : PartialDiffeomorph I J M N ∞) (s : Set M) (hs : IsOpen s) :
    PartialDiffeomorph I J M N ∞ where
  __ := e.toOpenPartialHomeomorph.restrOpen s hs
  contMDiffOn_toFun := e.contMDiffOn_toFun.mono Set.inter_subset_left
  contMDiffOn_invFun := e.contMDiffOn_invFun.mono Set.inter_subset_left

private def centeredLinearDiffeomorph
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (a : E) : E ≃ₘ[ℝ] F where
  toEquiv :=
    { toFun := fun x ↦ e (x - a)
      invFun := fun y ↦ e.symm y + a
      left_inv := by intro x; simp
      right_inv := by intro y; simp }
  contMDiff_toFun :=
    (e.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff
  contMDiff_invFun :=
    (e.symm.contDiff.add contDiff_const).contMDiff

private def shearPartialDiffeomorph
    {X Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (s : X → Z) (sx : Set X) (hsx : IsOpen sx)
    (hs : ContDiffOn ℝ ∞ s sx) :
    PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, X × Z) (X × Z) (X × Z) ∞ where
  toPartialEquiv :=
    { toFun := fun w ↦ (w.1, w.2 - s w.1)
      invFun := fun w ↦ (w.1, w.2 + s w.1)
      source := sx ×ˢ Set.univ
      target := sx ×ˢ Set.univ
      map_source' := by intro w hw; exact ⟨hw.1, Set.mem_univ _⟩
      map_target' := by intro w hw; exact ⟨hw.1, Set.mem_univ _⟩
      left_inv' := by intro w hw; ext <;> simp
      right_inv' := by intro w hw; ext <;> simp }
  open_source := hsx.prod isOpen_univ
  open_target := hsx.prod isOpen_univ
  contMDiffOn_toFun := by
    simpa [Function.comp_def] using
      (contDiffOn_fst.prodMk
        (contDiffOn_snd.sub
          (hs.comp contDiffOn_fst (fun _ (hw : _ ∈ sx ×ˢ Set.univ) ↦ hw.1)))).contMDiffOn
  contMDiffOn_invFun := by
    simpa [Function.comp_def] using
      (contDiffOn_fst.prodMk
        (contDiffOn_snd.add
          (hs.comp contDiffOn_fst (fun _ (hw : _ ∈ sx ×ˢ Set.univ) ↦ hw.1)))).contMDiffOn

private lemma isInvertible_fderiv_symm_of_partialDiffeomorph
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    {y : F} (hy : y ∈ Φ.target) :
    (fderiv ℝ Φ.symm y).IsInvertible := by
  let x : E := Φ.symm y
  have hx : x ∈ Φ.source := Φ.map_target hy
  have hxy : Φ x = y := Φ.right_inv hy
  have hfor : ContDiffAt ℝ ∞ Φ x :=
    Φ.contMDiffOn_toFun.contDiffOn.contDiffAt (Φ.open_source.mem_nhds hx)
  have hinv : ContDiffAt ℝ ∞ Φ.symm y :=
    Φ.contMDiffOn_invFun.contDiffOn.contDiffAt (Φ.open_target.mem_nhds hy)
  have hright : (Φ ∘ Φ.symm) =ᶠ[nhds y] id := by
    filter_upwards [Φ.open_target.mem_nhds hy] with z hz
    exact Φ.right_inv hz
  have hleft : (Φ.symm ∘ Φ) =ᶠ[nhds x] id := by
    filter_upwards [Φ.open_source.mem_nhds hx] with z hz
    exact Φ.left_inv hz
  have hrightDeriv :
      (fderiv ℝ Φ x).comp (fderiv ℝ Φ.symm y) = ContinuousLinearMap.id ℝ F := by
    have hc := (hfor.differentiableAt (by simp)).hasFDerivAt.comp y
      (hinv.differentiableAt (by simp)).hasFDerivAt
    have hid : HasFDerivAt (Φ ∘ Φ.symm) (ContinuousLinearMap.id ℝ F) y :=
      (hasFDerivAt_id y).congr_of_eventuallyEq hright
    simpa [hxy] using hc.unique hid
  have hleftDeriv :
      (fderiv ℝ Φ.symm y).comp (fderiv ℝ Φ x) = ContinuousLinearMap.id ℝ E := by
    have hinv' : DifferentiableAt ℝ Φ.symm (Φ x) := by
      simpa [hxy] using (hinv.differentiableAt (by simp))
    have hc := hinv'.hasFDerivAt.comp x
      (hfor.differentiableAt (by simp)).hasFDerivAt
    have hid : HasFDerivAt (Φ.symm ∘ Φ) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).congr_of_eventuallyEq hleft
    simpa [hxy] using hc.unique hid
  exact ContinuousLinearMap.IsInvertible.of_inverse hleftDeriv hrightDeriv

section FixedChartRank

variable {m n : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m'" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n'" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

private lemma fderiv_writtenInExtChartAt_eq_inTangentCoordinates
    {F : M → N} (hF : MDifferentiable I_m' I_n' F) (p q : M)
    (hq : q ∈ (extChartAt I_m' p).source)
    (hFq : F q ∈ (extChartAt I_n' (F p)).source) :
    fderiv ℝ (writtenInExtChartAt I_m' I_n' p F)
        (extChartAt I_m' p q) =
      inTangentCoordinates I_m' I_n' id F (mfderiv I_m' I_n' F) p q := by
  let x := extChartAt I_m' p q
  have hxTarget : x ∈ (extChartAt I_m' p).target :=
    (extChartAt I_m' p).map_source hq
  have hinv : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I_m'
      (extChartAt I_m' p).symm x := by
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ,
      mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm hxTarget)
  have hinvx : (extChartAt I_m' p).symm x = q :=
    (extChartAt I_m' p).left_inv hq
  have hinvx_chart : (chartAt (EuclideanSpace ℝ (Fin m)) p).symm x = q := by
    simpa [extChartAt_coe_symm] using hinvx
  dsimp [x] at hinvx_chart
  have hFqmd : MDifferentiableAt I_m' I_n' F q := hF q
  have hFcomp : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I_n'
      (F ∘ (extChartAt I_m' p).symm) x := by
    exact hFqmd.comp_of_eq x hinv hinvx
  have hcod : MDifferentiableAt I_n' 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (extChartAt I_n' (F p)) (F q) :=
    mdifferentiableAt_extChartAt (by rwa [← extChartAt_source I_n'])
  have hcomp1 := mfderiv_comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (I' := I_m') (I'' := I_n') (f := (extChartAt I_m' p).symm) (g := F)
    x (by simpa [x, hinvx_chart] using hFqmd) hinv
  have hcomp2 := mfderiv_comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (I' := I_n') (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (f := F ∘ (extChartAt I_m' p).symm) (g := extChartAt I_n' (F p))
    x (by simpa [x, hinvx_chart] using hcod) hFcomp
  rw [mfderiv_eq_fderiv] at hcomp2
  rw [inTangentCoordinates_eq_mfderiv_comp
    (by rwa [← extChartAt_source I_m'])
    (by rwa [← extChartAt_source I_n'])]
  rw [hcomp1] at hcomp2
  dsimp [x] at hcomp2
  rw [hinvx_chart] at hcomp2
  simpa [writtenInExtChartAt, x, hinvx, Function.comp_assoc,
    ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ] using hcomp2

set_option maxHeartbeats 2000000 in
private lemma finrank_fderiv_writtenInExtChartAt
    {F : M → N} (hF : MDifferentiable I_m' I_n' F) (p q : M)
    (hq : q ∈ (extChartAt I_m' p).source)
    (hFq : F q ∈ (extChartAt I_n' (F p)).source) :
    Module.finrank ℝ
        (fderiv ℝ (writtenInExtChartAt I_m' I_n' p F)
          (extChartAt I_m' p q)).range =
      Manifold.rankAt I_m' I_n' F q := by
  rw [fderiv_writtenInExtChartAt_eq_inTangentCoordinates hF p q hq hFq]
  rw [Manifold.rankAt_eq_finrank_range_mfderiv]
  rw [inTangentCoordinates_eq_mfderiv_comp
    (by rwa [← extChartAt_source I_m'])
    (by rwa [← extChartAt_source I_n'])]
  simp only [id_eq]
  unfold TangentSpace
  let B := mfderiv I_n' (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (extChartAt I_n' (F p)) (F q)
  let A := mfderiv I_m' I_n' F q
  let C := mfderivWithin (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) I_m'
    (extChartAt I_m' p).symm (Set.range I_m') (extChartAt I_m' p q)
  have hB : B.IsInvertible := by
    simpa [B] using isInvertible_mfderiv_extChartAt hFq
  have hC : C.IsInvertible := by
    simpa [C] using
      isInvertible_mfderivWithin_extChartAt_symm
        ((extChartAt I_m' p).map_source hq)
  unfold TangentSpace at B A C hB hC
  change Module.finrank ℝ (B.comp (A.comp C)).range =
    Module.finrank ℝ A.range
  rw [finrank_range_comp_isInvertible_left B (A.comp C) hB]
  exact finrank_range_comp_isInvertible_right A C hC

end FixedChartRank

section RankTheorem

variable {m n r : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E_m" => EuclideanSpace ℝ (Fin m)
local notation "E_n" => EuclideanSpace ℝ (Fin n)
local notation "X" => EuclideanSpace ℝ (Fin r)
local notation "Y" => EuclideanSpace ℝ (Fin (m - r))
local notation "Z" => EuclideanSpace ℝ (Fin (n - r))

set_option maxHeartbeats 4000000

/-- Theorem 4.12: a smooth map of constant rank `r` has centered smooth local coordinates in which
its coordinate representative is the standard rank-`r` normal form. -/
-- Proof sketch: use the inverse function theorem on the first `r` output coordinates to build a
-- centered source chart in which the map looks like `(x, y) ↦ (x, R_tilde (x, y))`; the
-- constant-rank hypothesis forces `R_tilde` to be independent of `y`, and a final centered target
-- chart subtracts the
-- resulting graph term to obtain `rank_normal_form m n r`.
theorem constant_rank_local_coordinate_normal_form {F : M → N}
    (hFsmooth : ContMDiff I_m I_n ∞ F) (hFrank : Manifold.HasConstantRank I_m I_n F r) (p : M) :
    ∃ h : LocalCoordinateNormalFormAt F p (rank_normal_form m n r), True := by
  let A : E_m →L[ℝ] E_n := mfderiv I_m I_n F p
  unfold TangentSpace at A
  have hArank : Module.finrank ℝ A.range = r := by
    have hpRank := hFrank.2 p
    unfold Manifold.rankAt TangentSpace at hpRank
    simpa [A] using hpRank
  obtain ⟨hrm, hrn, d, c, hcoord⟩ := exists_rank_coordinates A hArank
  let g : E_m → E_n := writtenInExtChartAt I_m I_n p F
  let a : E_m := extChartAt I_m p p
  let b : E_n := extChartAt I_n (F p) (F p)
  let Ω0 : Set E_m := (extChartAt I_m p).target ∩
    (F ∘ (extChartAt I_m p).symm) ⁻¹' (extChartAt I_n (F p)).source
  let affine : (X × Y) → E_m := fun w ↦ d.symm w + a
  let Ω : Set (X × Y) := affine ⁻¹' Ω0
  let qfun : (X × Y) → (X × Z) := fun w ↦ c (g (affine w) - b)
  let G : (X × Y) → (X × Y) := fun w ↦ ((qfun w).1, w.2)
  have hΩ0_target : (extChartAt I_m p).target ∈ nhds a := by
    simpa [a, ModelWithCorners.Boundaryless.range_eq_univ] using
      extChartAt_target_mem_nhdsWithin (I := I_m) p
  have hΩ0_source :
      (F ∘ (extChartAt I_m p).symm) ⁻¹' (extChartAt I_n (F p)).source ∈ nhds a := by
    convert extChartAt_preimage_mem_nhds (I := I_m) (x := p)
      (hFsmooth.continuous.continuousAt.preimage_mem_nhds
        (extChartAt_source_mem_nhds (I := I_n) (F p))) using 1 <;>
      ext x <;> rfl
  have hΩ0 : Ω0 ∈ nhds a := Filter.inter_mem hΩ0_target hΩ0_source
  have haffine_cont : Continuous affine := by
    exact d.symm.continuous.add continuous_const
  have haffine_zero : affine 0 = a := by simp [affine]
  have hΩ : Ω ∈ nhds (0 : X × Y) := by
    have hΩ0' : Ω0 ∈ nhds (affine 0) := by simpa [haffine_zero] using hΩ0
    simpa [Ω] using haffine_cont.continuousAt.preimage_mem_nhds hΩ0'
  have hgΩ0 : ContDiffOn ℝ ∞ g Ω0 := by
    simpa [g, Ω0] using
      writtenInExtChartAt_contDiffOn_of_contMDiff
        (I := I_m) (J := I_n) (n := ∞) (f := F) (p := p) hFsmooth
  have haffine_smooth : ContDiff ℝ ∞ affine := by
    exact d.symm.contDiff.add contDiff_const
  have hqΩ : ContDiffOn ℝ ∞ qfun Ω := by
    have hgin : ContDiffOn ℝ ∞ (fun w ↦ g (affine w)) Ω :=
      hgΩ0.comp haffine_smooth.contDiffOn (fun _ hw ↦ hw)
    have hsub : ContDiffOn ℝ ∞ (fun w ↦ g (affine w) - b) Ω :=
      hgin.sub contDiffOn_const
    simpa [qfun, Function.comp_def] using
      c.contDiff.contDiffOn.comp hsub (fun _ _ ↦ Set.mem_univ _)
  have hgDeriv : HasFDerivAt g A a := by
    simpa [g, A, a] using
      writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint
        (I := I_m) (J := I_n) (f := F) (p := p)
        BoundarylessManifold.isInteriorPoint
        (hFsmooth.contMDiffAt.mdifferentiableAt (by simp)).hasMFDerivAt
  have haffineDeriv : HasFDerivAt affine (d.symm : (X × Y) →L[ℝ] E_m) 0 := by
    simpa [affine] using d.symm.hasFDerivAt.add_const a
  let q' : (X × Y) →L[ℝ] (X × Z) :=
    (c : E_n →L[ℝ] (X × Z)).comp
      (A.comp (d.symm : (X × Y) →L[ℝ] E_m))
  have hqDeriv : HasFDerivAt qfun q' 0 := by
    have hgDeriv' : HasFDerivAt g A (affine 0) := by
      simpa [haffine_zero] using hgDeriv
    have h1 := hgDeriv'.comp (0 : X × Y) haffineDeriv
    have h2 := h1.sub_const b
    have h3 := c.hasFDerivAt.comp (0 : X × Y) h2
    simpa [qfun, affine, q', Function.comp_def] using h3
  have hnormal : ∀ w : X × Y, q' w = (w.1, 0) := by
    intro w
    simpa [q'] using hcoord (d.symm w)
  let L : (X × Y) →L[ℝ] (X × Y) :=
    ((ContinuousLinearMap.fst ℝ X Z).comp q').prod
      (ContinuousLinearMap.snd ℝ X Y)
  have hGDerivL : HasFDerivAt G L 0 := by
    simpa [G, L] using
      hqDeriv.fst.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (E := X) (F := Y))
  have hL_apply : ∀ w : X × Y, L w = w := by
    intro w
    change ((q' w).1, w.2) = w
    rw [hnormal]
  have hLbij : Function.Bijective L := by
    constructor
    · intro x y hxy
      rw [hL_apply x, hL_apply y] at hxy
      exact hxy
    · intro y
      exact ⟨y, hL_apply y⟩
  let eG : (X × Y) ≃L[ℝ] (X × Y) :=
    (LinearEquiv.ofBijective L.toLinearMap hLbij).toContinuousLinearEquiv
  have heG : (eG : (X × Y) →L[ℝ] (X × Y)) = L := by
    rfl
  have hGDeriv : HasFDerivAt G (eG : (X × Y) →L[ℝ] (X × Y)) 0 := by
    rw [heG]
    exact hGDerivL
  have hGΩ : ContDiffOn ℝ ∞ G Ω := by
    simpa [G] using hqΩ.fst.prodMk contDiffOn_snd
  have hGAt : ContDiffAt ℝ ∞ G 0 := hGΩ.contDiffAt hΩ
  have hGInv : (fderiv ℝ G 0).IsInvertible := by
    rw [hGDeriv.fderiv]
    exact ⟨eG, rfl⟩
  obtain ⟨Ψ, h0Ψ, hΨΩ, _hΨtarget, hΨeq⟩ :=
    model_partialDiffeomorph_of_inverse_function_theorem
      (𝕜 := ℝ) (E := X × Y) (F := X × Y)
      (g := G) (a := 0) (Ω := Ω) (T := Set.univ)
      (f' := eG)
      hΩ hGΩ (fun _ _ ↦ Set.mem_univ _) hGAt hGDeriv (by simp) hGInv
  have hgbase : g a = b := by
    simp only [g, a, b, writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt I_m p).left_inv (mem_extChartAt_source p)]
  have hqzero : qfun 0 = 0 := by
    simp [qfun, haffine_zero, hgbase]
  have hGzero : G 0 = 0 := by simp [G, hqzero]
  have hΨzero : Ψ 0 = 0 := by
    rw [← hΨeq h0Ψ, hGzero]
  have hzero_target : (0 : X × Y) ∈ Ψ.target := by
    rw [← hΨzero]
    exact Ψ.map_source h0Ψ
  obtain ⟨ux, hux, uy, huy, hprod⟩ :=
    mem_nhds_prod_iff.mp (Ψ.open_target.mem_nhds hzero_target)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hux
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp huy
  let sx : Set X := Metric.ball 0 ε
  let sy : Set Y := Metric.ball 0 δ
  have hsxopen : IsOpen sx := Metric.isOpen_ball
  have hsyopen : IsOpen sy := Metric.isOpen_ball
  have hzerosx : (0 : X) ∈ sx := by simpa [sx] using hε
  have hzerosy : (0 : Y) ∈ sy := by simpa [sy] using hδ
  have hbox : sx ×ˢ sy ⊆ Ψ.target := by
    intro w hw
    exact hprod ⟨hεsub hw.1, hδsub hw.2⟩
  let k : (X × Y) → (X × Z) := fun z ↦ qfun (Ψ.symm z)
  have hΨsymm_box : ContDiffOn ℝ ∞ Ψ.symm (sx ×ˢ sy) := by
    exact Ψ.contMDiffOn_invFun.contDiffOn.mono hbox
  have hkbox : ContDiffOn ℝ ∞ k (sx ×ˢ sy) := by
    exact hqΩ.comp hΨsymm_box (fun z hz ↦
      hΨΩ (Ψ.map_target (hbox hz)))
  have hkhead : Set.EqOn (fun z ↦ (k z).1) Prod.fst (sx ×ˢ sy) := by
    intro z hz
    have hzTarget := hbox hz
    have hzinv : Ψ.symm z ∈ Ψ.source := Ψ.map_target hzTarget
    have hright : Ψ (Ψ.symm z) = z := Ψ.right_inv hzTarget
    have hGΨ : G (Ψ.symm z) = Ψ (Ψ.symm z) := hΨeq hzinv
    change (qfun (Ψ.symm z)).1 = z.1
    exact (congrArg Prod.fst hGΨ).trans (congrArg Prod.fst hright)
  have hΩ0open : IsOpen Ω0 := by
    have hcont : ContinuousOn (F ∘ (extChartAt I_m p).symm)
        (extChartAt I_m p).target :=
      hFsmooth.continuous.continuousOn.comp
        (continuousOn_extChartAt_symm p) (fun _ _ ↦ Set.mem_univ _)
    exact hcont.isOpen_inter_preimage (isOpen_extChartAt_target p)
      (isOpen_extChartAt_source (F p))
  have hΩopen : IsOpen Ω := by
    exact hΩ0open.preimage haffine_cont
  have hrank_q : ∀ t ∈ Ω,
      Module.finrank ℝ (fderiv ℝ qfun t).range = r := by
    intro t ht
    have hxt : affine t ∈ Ω0 := ht
    let qM : M := (extChartAt I_m p).symm (affine t)
    have hqMsource : qM ∈ (extChartAt I_m p).source :=
      (extChartAt I_m p).map_target hxt.1
    have hright : extChartAt I_m p qM = affine t :=
      (extChartAt I_m p).right_inv hxt.1
    have hFqM : F qM ∈ (extChartAt I_n (F p)).source := by
      simpa [qM] using hxt.2
    have hgRank0 := finrank_fderiv_writtenInExtChartAt
      hFrank.1 p qM hqMsource hFqM
    have hgRank : Module.finrank ℝ (fderiv ℝ g (affine t)).range = r := by
      rw [hFrank.2 qM] at hgRank0
      change Module.finrank ℝ
        (fderiv ℝ (writtenInExtChartAt I_m I_n p F) (affine t)).range = r
      rw [← hright]
      exact hgRank0
    have haffDeriv_t : HasFDerivAt affine
        (d.symm : (X × Y) →L[ℝ] E_m) t := by
      simpa [affine] using d.symm.hasFDerivAt.add_const a
    have hgAt_t : HasFDerivAt g (fderiv ℝ g (affine t)) (affine t) :=
      ((hgΩ0.contDiffAt (hΩ0open.mem_nhds hxt)).differentiableAt (by simp)).hasFDerivAt
    have hqAt_t : HasFDerivAt qfun
        ((c : E_n →L[ℝ] (X × Z)).comp
          ((fderiv ℝ g (affine t)).comp (d.symm : (X × Y) →L[ℝ] E_m))) t := by
      have h1 := hgAt_t.comp t haffDeriv_t
      have h2 := h1.sub_const b
      have h3 := c.hasFDerivAt.comp t h2
      simpa [qfun, affine, Function.comp_def] using h3
    rw [hqAt_t.fderiv]
    rw [finrank_range_comp_isInvertible_left
      (c : E_n →L[ℝ] (X × Z))
      ((fderiv ℝ g (affine t)).comp (d.symm : (X × Y) →L[ℝ] E_m))
      (by exact ⟨c, rfl⟩)]
    rw [finrank_range_comp_isInvertible_right
      (fderiv ℝ g (affine t)) (d.symm : (X × Y) →L[ℝ] E_m)
      (by exact ⟨d.symm, rfl⟩)]
    exact hgRank
  have hrank_k : ∀ z ∈ sx ×ˢ sy,
      Module.finrank ℝ (fderiv ℝ k z).range = r := by
    intro z hz
    have hzTarget := hbox hz
    have hzinv : Ψ.symm z ∈ Ψ.source := Ψ.map_target hzTarget
    have hqAt : DifferentiableAt ℝ qfun (Ψ.symm z) :=
      (hqΩ.differentiableOn (by simp) (Ψ.symm z) (hΨΩ hzinv)).differentiableAt
        (hΩopen.mem_nhds (hΨΩ hzinv))
    have hsymmAt : DifferentiableAt ℝ Ψ.symm z :=
      (hΨsymm_box.differentiableOn (by simp) z hz).differentiableAt
        ((hsxopen.prod hsyopen).mem_nhds hz)
    have hkformula : fderiv ℝ k z =
        (fderiv ℝ qfun (Ψ.symm z)).comp (fderiv ℝ Ψ.symm z) := by
      simpa [k, Function.comp_def] using (hqAt.hasFDerivAt.comp z hsymmAt.hasFDerivAt).fderiv
    rw [hkformula]
    rw [finrank_range_comp_isInvertible_right
      (fderiv ℝ qfun (Ψ.symm z)) (fderiv ℝ Ψ.symm z)
      (isInvertible_fderiv_symm_of_partialDiffeomorph Ψ hzTarget)]
    exact hrank_q (Ψ.symm z) (hΨΩ hzinv)
  have hkindep : ∀ x ∈ sx, ∀ y ∈ sy, (k (x, y)).2 = (k (x, 0)).2 :=
    tail_independent_on_product hsxopen hsyopen (convex_ball 0 δ) hzerosy
      (hkbox.differentiableOn (by simp)) hkhead (by
        intro z hz
        simpa using hrank_k z hz)
  let s : X → Z := fun x ↦ (k (x, 0)).2
  have hs : ContDiffOn ℝ ∞ s sx := by
    have hslice : ContDiffOn ℝ ∞ (fun x : X ↦ (x, (0 : Y))) sx :=
      contDiffOn_id.prodMk contDiffOn_const
    exact hkbox.snd.comp hslice (fun x hx ↦ ⟨hx, hzerosy⟩)
  let S := shearPartialDiffeomorph s sx hsxopen hs
  let D := preferredChartPartialDiffeomorph (I := I_m) p
  let Ld := centeredLinearDiffeomorph d a
  let R := D.trans Ld.toPartialDiffeomorph
  let P := R.trans Ψ
  have hRp : R p = 0 := by
    change Ld (D p) = 0
    change d (extChartAt I_m p p - a) = 0
    rw [show extChartAt I_m p p = a from rfl]
    simp
  have hpP : p ∈ P.source := by
    change p ∈ (R.toPartialEquiv.trans Ψ.toPartialEquiv).source
    rw [PartialEquiv.trans_source]
    refine ⟨?_, ?_⟩
    · change p ∈ (D.toPartialEquiv.trans Ld.toEquiv.toPartialEquiv).source
      rw [PartialEquiv.trans_source]
      exact ⟨mem_extChartAt_source p, Set.mem_univ _⟩
    · change R p ∈ Ψ.source
      rw [hRp]
      exact h0Ψ
  have hPp : P p = 0 := by
    change Ψ (R p) = 0
    rw [hRp]
    exact hΨzero
  have hboxP : sx ×ˢ sy ⊆ P.target := by
    intro z hz
    change z ∈ (R.toPartialEquiv.trans Ψ.toPartialEquiv).target
    rw [PartialEquiv.trans_target]
    refine ⟨hbox hz, ?_⟩
    change Ψ.symm z ∈ (D.toPartialEquiv.trans Ld.toEquiv.toPartialEquiv).target
    rw [PartialEquiv.trans_target]
    refine ⟨Set.mem_univ _, ?_⟩
    change d.symm (Ψ.symm z) + a ∈ (extChartAt I_m p).target
    exact (hΨΩ (Ψ.map_target (hbox hz))).1
  let Rbox := P.symm.restrOpen (sx ×ˢ sy) (hsxopen.prod hsyopen)
  let Pbox := Rbox.symm
  have hPbox_target : Pbox.target = sx ×ˢ sy := by
    change P.target ∩ (sx ×ˢ sy) = sx ×ˢ sy
    exact Set.inter_eq_right.mpr hboxP
  have hzero_box : (0 : X × Y) ∈ sx ×ˢ sy := ⟨hzerosx, hzerosy⟩
  have h0Rbox : (0 : X × Y) ∈ Rbox.source := by
    change (0 : X × Y) ∈ P.target ∩ (sx ×ˢ sy)
    exact ⟨by rw [← hPp]; exact P.map_source hpP, hzero_box⟩
  have hpPbox : p ∈ Pbox.source := by
    have hm := Rbox.map_source h0Rbox
    have hPinv : P.symm 0 = p := by
      rw [← hPp]
      exact P.left_inv hpP
    change p ∈ Rbox.target
    rw [← hPinv]
    exact hm
  have hPboxp : Pbox p = 0 := by
    change P p = 0
    exact hPp
  let Dom := Pbox.trans (finSplit hrm).symm.toDiffeomorph.toPartialDiffeomorph
  let C := preferredChartPartialDiffeomorph (I := I_n) (F p)
  let Lc := centeredLinearDiffeomorph c b
  let Q0 := C.trans Lc.toPartialDiffeomorph
  let Q1 := Q0.trans S
  let Cod := Q1.trans (finSplit hrn).symm.toDiffeomorph.toPartialDiffeomorph
  have hQ0Fp : Q0 (F p) = 0 := by
    change c (extChartAt I_n (F p) (F p) - b) = 0
    rw [show extChartAt I_n (F p) (F p) = b from rfl]
    simp

  have hΨinvzero : Ψ.symm (0 : X × Y) = 0 := by
    have hleft := Ψ.left_inv h0Ψ
    rwa [hΨzero] at hleft
  have hkzero : k (0 : X × Y) = 0 := by
    change qfun (Ψ.symm (0 : X × Y)) = 0
    rw [hΨinvzero, hqzero]
  have hszero : s 0 = 0 := by
    have h00 : (0 : X × Y) = (0, 0) := Prod.ext rfl rfl
    simp only [s]
    rw [← h00]
    exact congrArg Prod.snd hkzero
  have hQ1Fp : Q1 (F p) = 0 := by
    change S (Q0 (F p)) = 0
    rw [hQ0Fp]
    change ((0 : X × Z).1, (0 : X × Z).2 - s (0 : X × Z).1) = 0
    simp [hszero]
  have hFpQ0 : F p ∈ Q0.source := by
    change F p ∈ (C.toPartialEquiv.trans Lc.toEquiv.toPartialEquiv).source
    rw [PartialEquiv.trans_source]
    exact ⟨mem_extChartAt_source (F p), Set.mem_univ _⟩
  have hFpQ1 : F p ∈ Q1.source := by
    refine ⟨hFpQ0, ?_⟩
    change Q0 (F p) ∈ S.source
    rw [hQ0Fp]
    exact ⟨hzerosx, Set.mem_univ _⟩
  have hFpCod : F p ∈ Cod.source := by
    change F p ∈ (Q1.toPartialEquiv.trans
      (finSplit hrn).symm.toEquiv.toPartialEquiv).source
    rw [PartialEquiv.trans_source]
    exact ⟨hFpQ1, Set.mem_univ _⟩
  have hCodFp : Cod (F p) = 0 := by
    change (finSplit hrn).symm (Q1 (F p)) = 0
    rw [hQ1Fp]
    simp
  have hpDom : p ∈ Dom.source := by
    change p ∈ (Pbox.toPartialEquiv.trans
      (finSplit hrm).symm.toEquiv.toPartialEquiv).source
    rw [PartialEquiv.trans_source]
    exact ⟨hpPbox, Set.mem_univ _⟩
  have hDomp : Dom p = 0 := by
    change (finSplit hrm).symm (Pbox p) = 0
    rw [hPboxp]
    simp
  have hcoordinate : ∀ x ∈ Pbox.source,
      F x ∈ Q1.source ∧ Q1 (F x) = ((Pbox x).1, 0) := by
    intro x hx
    have hxRbox : x ∈ Rbox.target := hx
    have hxP : x ∈ P.source := by
      change x ∈ (P.symm.toPartialEquiv.restr (sx ×ˢ sy)).target at hxRbox
      rw [PartialEquiv.restr_target] at hxRbox
      exact hxRbox.1
    have hzbox : Pbox x ∈ sx ×ˢ sy := by
      rw [← hPbox_target]
      exact Pbox.map_source hx
    have hxP' : x ∈ (R.toPartialEquiv.trans Ψ.toPartialEquiv).source := hxP
    rw [PartialEquiv.trans_source] at hxP'
    have hxR : x ∈ R.source := hxP'.1
    have hwsource : R x ∈ Ψ.source := hxP'.2
    have hxR' : x ∈ (D.toPartialEquiv.trans Ld.toEquiv.toPartialEquiv).source := hxR
    rw [PartialEquiv.trans_source] at hxR'
    have hxD : x ∈ (extChartAt I_m p).source := hxR'.1
    let w : X × Y := R x
    let z : X × Y := Pbox x
    have hzP : z = P x := rfl
    have hzΨ : z = Ψ w := by
      rw [hzP]
      rfl
    have hΨinv : Ψ.symm z = w := by
      rw [hzΨ]
      exact Ψ.left_inv hwsource
    have hwΩ : w ∈ Ω := hΨΩ hwsource
    have haffw : affine w = extChartAt I_m p x := by
      change d.symm (R x) + a = extChartAt I_m p x
      change d.symm (d (extChartAt I_m p x - a)) + a = extChartAt I_m p x
      simp
    have hFxsource : F x ∈ (extChartAt I_n (F p)).source := by
      have hwΩ0 : affine w ∈ Ω0 := hwΩ
      have hmem := hwΩ0.2
      rw [haffw] at hmem
      change F ((extChartAt I_m p).symm (extChartAt I_m p x)) ∈
          (extChartAt I_n (F p)).source at hmem
      simpa only [(extChartAt I_m p).left_inv hxD] using hmem
    have hgx : g (affine w) = extChartAt I_n (F p) (F x) := by
      change extChartAt I_n (F p)
        (F ((extChartAt I_m p).symm (affine w))) = _
      rw [haffw, (extChartAt I_m p).left_inv hxD]
    have hkz : k z = Q0 (F x) := by
      change qfun (Ψ.symm z) = c (extChartAt I_n (F p) (F x) - b)
      rw [hΨinv]
      simp [qfun, hgx]
    have hQ0source : F x ∈ Q0.source := by
      change F x ∈ (C.toPartialEquiv.trans Lc.toEquiv.toPartialEquiv).source
      rw [PartialEquiv.trans_source]
      exact ⟨hFxsource, Set.mem_univ _⟩
    have hkfst : (k z).1 = z.1 := hkhead hzbox
    have hksnd : (k z).2 = s z.1 := by
      exact hkindep z.1 hzbox.1 z.2 hzbox.2
    have hQ1source : F x ∈ Q1.source := by
      refine ⟨hQ0source, ?_⟩
      change Q0 (F x) ∈ S.source
      rw [← hkz]
      exact ⟨by simpa [hkfst] using hzbox.1, Set.mem_univ _⟩
    refine ⟨hQ1source, ?_⟩
    change S (Q0 (F x)) = (z.1, 0)
    rw [← hkz]
    change ((k z).1, (k z).2 - s (k z).1) = (z.1, 0)
    rw [hkfst, hksnd]
    simp
  let domChart := Dom.toOpenPartialHomeomorph
  let codChart := Cod.toOpenPartialHomeomorph
  have hmaps : MapsTo F domChart.source codChart.source := by
    intro x hx
    have hx' : x ∈ Pbox.source := by
      change x ∈ (Pbox.toPartialEquiv.trans
        (finSplit hrm).symm.toEquiv.toPartialEquiv).source at hx
      rw [PartialEquiv.trans_source] at hx
      exact hx.1
    have hq1 := (hcoordinate x hx').1
    change F x ∈ (Q1.toPartialEquiv.trans
      (finSplit hrn).symm.toEquiv.toPartialEquiv).source
    rw [PartialEquiv.trans_source]
    exact ⟨hq1, Set.mem_univ _⟩
  have heq : EqOn (codChart ∘ F ∘ domChart.symm)
      (rank_normal_form m n r) domChart.target := by
    intro y hy
    let x : M := domChart.symm y
    have hx : x ∈ domChart.source := domChart.map_target hy
    have hxPbox : x ∈ Pbox.source := by
      change x ∈ (Pbox.toPartialEquiv.trans
        (finSplit hrm).symm.toEquiv.toPartialEquiv).source at hx
      rw [PartialEquiv.trans_source] at hx
      exact hx.1
    have hcoordx := hcoordinate x hxPbox
    have hdomright : domChart x = y := domChart.right_inv hy
    have hz : Pbox x = finSplit hrm y := by
      apply (finSplit hrm).symm.injective
      have hcoe : (finSplit hrm).symm (Pbox x) = Dom x := by
        change (finSplit hrm).symm (Pbox x) =
          (finSplit hrm).symm.toDiffeomorph.toPartialDiffeomorph (Pbox x)
        simp [ContinuousLinearEquiv.coe_toDiffeomorph, Diffeomorph.toPartialDiffeomorph]
      rw [hcoe, show Dom x = y from hdomright, ContinuousLinearEquiv.symm_apply_apply]
    have hcodval : codChart (F x) =
        (finSplit hrn).symm ((Pbox x).1, 0) := by
      change (finSplit hrn).symm (Q1 (F x)) = _
      rw [hcoordx.2]
    change codChart (F x) = rank_normal_form m n r y
    rw [hcodval, hz]
    apply (finSplit hrn).injective
    rw [(finSplit hrn).apply_symm_apply]
    exact (finSplit_rank_normal_form hrm hrn y).symm
  let h : LocalCoordinateNormalFormAt F p (rank_normal_form m n r) :=
    { domChart := domChart
      codChart := codChart
      domChart_mem_maximalAtlas :=
        domChart.mem_maximalAtlas_of_contMDiffOn
          Dom.contMDiffOn_toFun Dom.contMDiffOn_invFun
      codChart_mem_maximalAtlas :=
        codChart.mem_maximalAtlas_of_contMDiffOn
          Cod.contMDiffOn_toFun Cod.contMDiffOn_invFun
      domChart_centered := ⟨hpDom, hDomp⟩
      codChart_centered := ⟨hFpCod, hCodFp⟩
      mapsTo := hmaps
      eqOn := heq }
  exact ⟨h, trivial⟩

/-- A smooth submersion admits centered local coordinates in which it becomes projection onto the
first `n` coordinates. -/
-- Proof sketch: specialize the rank theorem to the full target rank `r = n`; a smooth
-- submersion has surjective manifold derivative at every point, so the rank normal form becomes
-- the projection form of equation `(4.2)`.
theorem smooth_submersion_local_projection_form {F : M → N}
    (hF : Manifold.IsSmoothSubmersion
      I_m I_n F) (p : M) :
    ∃ h : LocalCoordinateNormalFormAt F p (rank_normal_form m n n), True := by
  have hrank : Manifold.HasConstantRank I_m I_n F n := by
    refine ⟨hF.contMDiff.mdifferentiable (by simp), ?_⟩
    intro q
    have hsurj := hF.surjective_mfderiv q
    unfold Manifold.rankAt TangentSpace
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
    simp
  exact constant_rank_local_coordinate_normal_form hF.contMDiff hrank p

/-- A smooth immersion admits centered local coordinates in which it becomes the standard
coordinate inclusion into the first `m` target coordinates. -/
-- Proof sketch: specialize the rank theorem to the full source rank `r = m`; in that case the
-- rank normal form is the inclusion form of equation `(4.3)`.
theorem smooth_immersion_local_inclusion_form {F : M → N}
    (hF : Manifold.IsImmersion
      I_m I_n ∞ F) (p : M) :
    ∃ h : LocalCoordinateNormalFormAt F p (rank_normal_form m n m), True := by
  have hrank : Manifold.HasConstantRank I_m I_n F m := by
    refine ⟨hF.contMDiff.mdifferentiable (by simp), ?_⟩
    intro q
    have hinj := hF.mfderiv_injective q
    change Module.finrank ℝ (mfderiv I_m I_n F q).range = m
    rw [LinearMap.finrank_range_of_inj hinj]
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m
    simp
  exact constant_rank_local_coordinate_normal_form hF.contMDiff hrank p

end RankTheorem
