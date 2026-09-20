import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_12
import LeeSmoothLib.Ch05.Sec05_29.Definition_5_29_extra_1

/-!
Analytic (`⊤`) local normal form at a regular point, for the Gram-fiber construction
of Example 8.47.  Copied from the C∞ RegularValueLocalNormalForm and honestly
generalized to analytic order; charts live in the `⊤` maximal atlas.
-/

noncomputable section

open Set
open scoped ContDiff Manifold InnerProductSpace

set_option backward.isDefEq.respectTransparency false

namespace AnalyticOrthogonalFiberNormalForm

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

private def preferredChartPartialDiffeomorph
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (x : M) : PartialDiffeomorph I 𝓘(ℝ, E) M E (⊤ : WithTop ℕ∞) where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (n := (⊤ : WithTop ℕ∞)) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

private def continuousLinearEquivDiffeomorphTop
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F (⊤ : WithTop ℕ∞) where
  toEquiv := e.toLinearEquiv.toEquiv
  contMDiff_toFun := e.contDiff.contMDiff
  contMDiff_invFun := e.symm.contDiff.contMDiff

private def centeredLinearDiffeomorph
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (a : E) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F (⊤ : WithTop ℕ∞) where
  toEquiv :=
    { toFun := fun x ↦ e (x - a)
      invFun := fun y ↦ e.symm y + a
      left_inv := by intro x; simp
      right_inv := by intro y; simp }
  contMDiff_toFun :=
    (e.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff
  contMDiff_invFun :=
    (e.symm.contDiff.add contDiff_const).contMDiff

universe uM uN

variable {m n : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) (⊤ : WithTop ℕ∞) M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N]

local notation "I_m" => 𝓡 m
local notation "I_n" => 𝓡 n
local notation "E_m" => EuclideanSpace ℝ (Fin m)
local notation "E_n" => EuclideanSpace ℝ (Fin n)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin (m - n))
local notation "Z" => EuclideanSpace ℝ (Fin (n - n))

/-- Analytic local coordinate normal form: charts belong to the `⊤` maximal atlas. -/
structure AnalyticLocalCoordinateNormalFormAt (F : M → N) (p : M)
    (normalForm : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) where
  domChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m))
  codChart : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n))
  domChart_mem_maximalAtlas :
    domChart ∈ IsManifold.maximalAtlas I_m (⊤ : WithTop ℕ∞) M
  codChart_mem_maximalAtlas :
    codChart ∈ IsManifold.maximalAtlas I_n (⊤ : WithTop ℕ∞) N
  domChart_centered : p ∈ domChart.source ∧ domChart p = 0
  codChart_centered : F p ∈ codChart.source ∧ codChart (F p) = 0
  mapsTo : MapsTo F domChart.source codChart.source
  eqOn : EqOn (codChart ∘ F ∘ domChart.symm) normalForm domChart.target

/-- At a point where the derivative is surjective, an analytic map has the projection normal form.
This is the direct inverse-function-theorem construction used by the regular-level theorem. -/
theorem at_of_surjective_mfderiv
    {F : M → N} (hF : ContMDiff I_m I_n (⊤ : WithTop ℕ∞) F) (p : M)
    (hp : Function.Surjective (mfderiv I_m I_n F p)) :
    ∃ h : AnalyticLocalCoordinateNormalFormAt F p (rank_normal_form m n n), True := by
  let A : E_m →L[ℝ] E_n := mfderiv I_m I_n F p
  unfold TangentSpace at A
  have hArank : Module.finrank ℝ A.range = n := by
    rw [LinearMap.range_eq_top.mpr hp, finrank_top]
    simp
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
      (hF.continuous.continuousAt.preimage_mem_nhds
        (extChartAt_source_mem_nhds (I := I_n) (F p))) using 1 <;>
      ext x <;> rfl
  have hΩ0 : Ω0 ∈ nhds a := Filter.inter_mem hΩ0_target hΩ0_source
  have haffine_cont : Continuous affine :=
    d.symm.continuous.add continuous_const
  have haffine_zero : affine 0 = a := by simp [affine]
  have hΩ : Ω ∈ nhds (0 : X × Y) := by
    have hΩ0' : Ω0 ∈ nhds (affine 0) := by simpa [haffine_zero] using hΩ0
    simpa [Ω] using haffine_cont.continuousAt.preimage_mem_nhds hΩ0'
  have hgΩ0 : ContDiffOn ℝ (⊤ : WithTop ℕ∞) g Ω0 := by
    simpa [g, Ω0] using
      writtenInExtChartAt_contDiffOn_of_contMDiff
        (I := I_m) (J := I_n) (n := (⊤ : WithTop ℕ∞)) (f := F) (p := p) hF
  have haffine_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) affine :=
    d.symm.contDiff.add contDiff_const
  have hqΩ : ContDiffOn ℝ (⊤ : WithTop ℕ∞) qfun Ω := by
    have hgin : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun w ↦ g (affine w)) Ω :=
      hgΩ0.comp haffine_smooth.contDiffOn (fun _ hw ↦ hw)
    have hsub : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun w ↦ g (affine w) - b) Ω :=
      hgin.sub contDiffOn_const
    simpa [qfun, Function.comp_def] using
      c.contDiff.contDiffOn.comp hsub (fun _ _ ↦ Set.mem_univ _)
  have hgDeriv : HasFDerivAt g A a := by
    simpa [g, A, a] using
      writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint
        (I := I_m) (J := I_n) (f := F) (p := p)
        BoundarylessManifold.isInteriorPoint
        (hF.contMDiffAt.mdifferentiableAt (by simp)).hasMFDerivAt
  have haffineDeriv :
      HasFDerivAt affine (d.symm : (X × Y) →L[ℝ] E_m) 0 := by
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
  have heG : (eG : (X × Y) →L[ℝ] (X × Y)) = L := rfl
  have hGDeriv : HasFDerivAt G (eG : (X × Y) →L[ℝ] (X × Y)) 0 := by
    rw [heG]
    exact hGDerivL
  have hGΩ : ContDiffOn ℝ (⊤ : WithTop ℕ∞) G Ω := by
    simpa [G] using hqΩ.fst.prodMk contDiffOn_snd
  have hGAt : ContDiffAt ℝ (⊤ : WithTop ℕ∞) G 0 := hGΩ.contDiffAt hΩ
  have hGInv : (fderiv ℝ G 0).IsInvertible := by
    rw [hGDeriv.fderiv]
    exact ⟨eG, rfl⟩
  obtain ⟨Ψ, h0Ψ, hΨΩ, _hΨtarget, hΨeq⟩ :=
    model_partialDiffeomorph_of_inverse_function_theorem
      (𝕜 := ℝ) (E := X × Y) (F := X × Y)
      (g := G) (a := 0) (Ω := Ω) (T := Set.univ) (f' := eG)
      hΩ hGΩ (fun _ _ ↦ Set.mem_univ _) hGAt hGDeriv (by simp) hGInv
  have hgbase : g a = b := by
    simp only [g, a, b, writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt I_m p).left_inv (mem_extChartAt_source p)]
  have hqzero : qfun 0 = 0 := by
    simp [qfun, haffine_zero, hgbase]
  have hGzero : G 0 = 0 := by simp [G, hqzero]
  have hΨzero : Ψ 0 = 0 := by
    rw [← hΨeq h0Ψ, hGzero]
  let domCenter :
      Diffeomorph I_m 𝓘(ℝ, X × Y) E_m (X × Y) (⊤ : WithTop ℕ∞) :=
    centeredLinearDiffeomorph d a
  let domFinish :
      Diffeomorph 𝓘(ℝ, X × Y) I_m (X × Y) E_m (⊤ : WithTop ℕ∞) :=
    continuousLinearEquivDiffeomorphTop (finSplit hrm).symm
  let domP : PartialDiffeomorph I_m I_m M E_m (⊤ : WithTop ℕ∞) :=
    (((preferredChartPartialDiffeomorph (I := I_m) p).trans
      domCenter.toPartialDiffeomorph).trans Ψ).trans domFinish.toPartialDiffeomorph
  let codLinear : E_n ≃L[ℝ] E_n := c.trans (finSplit hrn).symm
  let codCenter :
      Diffeomorph I_n I_n E_n E_n (⊤ : WithTop ℕ∞) :=
    centeredLinearDiffeomorph codLinear b
  let codP : PartialDiffeomorph I_n I_n N E_n (⊤ : WithTop ℕ∞) :=
    (preferredChartPartialDiffeomorph (I := I_n) (F p)).trans
      codCenter.toPartialDiffeomorph
  let domChart := domP.toOpenPartialHomeomorph
  let codChart := codP.toOpenPartialHomeomorph
  have hpDom : p ∈ domChart.source := by
    change p ∈ domP.source
    simp [domP, domCenter, domFinish, preferredChartPartialDiffeomorph,
      Diffeomorph.toPartialDiffeomorph, centeredLinearDiffeomorph, a, h0Ψ]
  have hFpCod : F p ∈ codChart.source := by
    change F p ∈ codP.source
    change
      F p ∈ (extChartAt I_n (F p)).source ∧
        codCenter (extChartAt I_n (F p) (F p)) ∈ Set.univ
    exact ⟨mem_extChartAt_source (F p), Set.mem_univ _⟩
  have hdomZero : domChart p = 0 := by
    change domP p = 0
    change domFinish (Ψ (domCenter (extChartAt I_m p p))) = 0
    have hcenter : domCenter (extChartAt I_m p p) = 0 := by
      change d (extChartAt I_m p p - a) = 0
      simp [a]
    rw [hcenter, hΨzero]
    change (finSplit hrm).symm 0 = 0
    simp
  have hcodZero : codChart (F p) = 0 := by
    change codP (F p) = 0
    change codCenter (extChartAt I_n (F p) (F p)) = 0
    change codLinear (extChartAt I_n (F p) (F p) - b) = 0
    simp [b]
  have hdomMax : domChart ∈ IsManifold.maximalAtlas I_m (⊤ : WithTop ℕ∞) M :=
    domChart.mem_maximalAtlas_of_contMDiffOn
      domP.contMDiffOn_toFun domP.contMDiffOn_invFun
  have hcodMax : codChart ∈ IsManifold.maximalAtlas I_n (⊤ : WithTop ℕ∞) N :=
    codChart.mem_maximalAtlas_of_contMDiffOn
      codP.contMDiffOn_toFun codP.contMDiffOn_invFun
  have hmaps : MapsTo F domChart.source codChart.source := by
    intro x hx
    change F x ∈ codP.source
    change x ∈ domP.source at hx
    rcases hx with ⟨⟨⟨hxExt, _⟩, hxΨ⟩, _⟩
    have hwΩ : d (extChartAt I_m p x - a) ∈ Ω :=
      hΨΩ hxΨ
    have haff :
        affine (d (extChartAt I_m p x - a)) = extChartAt I_m p x := by
      simp [affine]
    have hFx : F x ∈ (extChartAt I_n (F p)).source := by
      have hmem := hwΩ.2
      rw [haff] at hmem
      change
        F ((extChartAt I_m p).symm (extChartAt I_m p x)) ∈
          (extChartAt I_n (F p)).source at hmem
      simpa only [(extChartAt I_m p).left_inv hxExt] using hmem
    change
      F x ∈ (extChartAt I_n (F p)).source ∧
        codCenter (extChartAt I_n (F p) (F x)) ∈ Set.univ
    exact ⟨hFx, Set.mem_univ _⟩
  have heq :
      EqOn (codChart ∘ F ∘ domChart.symm) (rank_normal_form m n n)
        domChart.target := by
    intro z hz
    let x : M := domChart.symm z
    have hxSource : x ∈ domChart.source := domChart.symm.map_source hz
    have hzx : domChart x = z := domChart.right_inv hz
    have hxExt : x ∈ (extChartAt I_m p).source := by
      change x ∈ domP.source at hxSource
      exact hxSource.1.1.1
    let w : X × Y := d (extChartAt I_m p x - a)
    have hwΨ : w ∈ Ψ.source := by
      change x ∈ domP.source at hxSource
      exact hxSource.1.2
    have hΨw : Ψ w = G w := (hΨeq hwΨ).symm
    have haffw : affine w = extChartAt I_m p x := by
      simp [w, affine]
    have hgx :
        g (affine w) = extChartAt I_n (F p) (F x) := by
      change
        extChartAt I_n (F p)
            (F ((extChartAt I_m p).symm (affine w))) =
          extChartAt I_n (F p) (F x)
      rw [haffw, (extChartAt I_m p).left_inv hxExt]
    have hqtail : (qfun w).2 = 0 := by
      ext i
      exact Fin.elim0 (Fin.cast (by omega) i)
    have hcodApply :
        codChart (F x) = (finSplit hrn).symm (qfun w) := by
      change codP (F x) = _
      change
        codCenter (extChartAt I_n (F p) (F x)) =
          (finSplit hrn).symm (qfun w)
      change
        (finSplit hrn).symm
            (c (extChartAt I_n (F p) (F x) - b)) =
          (finSplit hrn).symm (c (g (affine w) - b))
      rw [hgx]
    have hdomApply :
        domChart x = (finSplit hrm).symm (G w) := by
      change domP x = _
      change
        domFinish (Ψ (domCenter (extChartAt I_m p x))) =
          (finSplit hrm).symm (G w)
      have hcenterx : domCenter (extChartAt I_m p x) = w := by
        change d (extChartAt I_m p x - a) = w
        rfl
      rw [hcenterx, hΨw]
      rfl
    change codChart (F x) = rank_normal_form m n n z
    rw [← hzx, hcodApply, hdomApply]
    apply (finSplit hrn).injective
    rw [finSplit_rank_normal_form hrm hrn]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    change qfun w = ((qfun w).1, 0)
    apply Prod.ext
    · rfl
    · exact hqtail
  refine ⟨{
    domChart := domChart
    codChart := codChart
    domChart_mem_maximalAtlas := hdomMax
    codChart_mem_maximalAtlas := hcodMax
    domChart_centered := ⟨hpDom, hdomZero⟩
    codChart_centered := ⟨hFpCod, hcodZero⟩
    mapsTo := hmaps
    eqOn := heq }, trivial⟩

/-- Coordinate permutation sending the first `r` coordinates to the tail, so a rank-`r`
projection fiber becomes a Euclidean `m - r` slice. -/
private def constantRankFiberPermIndex (m r : ℕ) (hr : r ≤ m) : Fin m ≃ Fin m :=
  (finCongr (Nat.sub_add_cancel hr).symm).trans <|
    finAddFlip.trans (finCongr (Nat.add_sub_of_le hr))

private def constantRankFiberPerm (m r : ℕ) (hr : r ≤ m) :
    EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (constantRankFiberPermIndex m r hr).symm

private theorem constantRankFiberPerm_tail {m r : ℕ} (hr : r ≤ m)
    (z : EuclideanSpace ℝ (Fin m)) (i : Fin r) :
    constantRankFiberPerm m r hr z
      (Fin.cast (Nat.sub_add_cancel hr) (Fin.natAdd (m - r) i)) =
        z (Fin.castLE hr i) := by
  have hidx :
      constantRankFiberPermIndex m r hr
          (Fin.cast (Nat.sub_add_cancel hr) (Fin.natAdd (m - r) i)) =
        Fin.castLE hr i := by
    apply Fin.ext
    simp [constantRankFiberPermIndex]
  simpa [constantRankFiberPerm] using congrArg (fun j : Fin m => z j) hidx

private theorem constantRankFiberPerm_mem_groupoid {m r : ℕ} (hr : r ≤ m) :
    (constantRankFiberPerm m r hr).toHomeomorph.toOpenPartialHomeomorph ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa [modelWithCornersSelf_coe] using
      (constantRankFiberPerm m r hr).contDiff.contDiffOn
  · simpa [modelWithCornersSelf_coe] using
      (constantRankFiberPerm m r hr).symm.contDiff.contDiffOn

private theorem constantRankNormalForm_apply_of_lt
    {m n r : ℕ} (i : Fin n) (hri : (i : ℕ) < r) (hmi : (i : ℕ) < m)
    (x : EuclideanSpace ℝ (Fin m)) :
    rank_normal_form m n r x i = x ⟨i, hmi⟩ := by
  simp [rank_normal_form, hri, hmi]

/-- A genuine analytic rank-normal-form chart cuts its fiber out as an analytic Euclidean slice. -/
theorem analytic_rankNormalForm_fiber_isSliceChart
    {F : M → N} {p : M} {c : N} {r : ℕ}
    (h : AnalyticLocalCoordinateNormalFormAt F p (rank_normal_form m n r))
    (hpc : F p = c) (hrm : r ≤ m) (hrn : r ≤ n) :
    (h.domChart.trans
      (constantRankFiberPerm m r hrm).toHomeomorph.toOpenPartialHomeomorph).IsSliceChart
        (F ⁻¹' {c}) (m - r) := by
  let chi := (constantRankFiberPerm m r hrm).toHomeomorph.toOpenPartialHomeomorph
  let e := h.domChart.trans chi
  have hchi : chi ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) :=
    constantRankFiberPerm_mem_groupoid hrm
  refine ⟨?_, ?_⟩
  · rw [IsManifold.mem_maximalAtlas_iff]
    intro e' he'
    have he'max : e' ∈ IsManifold.maximalAtlas (𝓡 m) (⊤ : WithTop ℕ∞) M :=
      IsManifold.subset_maximalAtlas he'
    have hleft : h.domChart.symm.trans e' ∈
        contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) :=
      IsManifold.compatible_of_mem_maximalAtlas h.domChart_mem_maximalAtlas he'max
    have hright : e'.symm.trans h.domChart ∈
        contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) :=
      IsManifold.compatible_of_mem_maximalAtlas he'max h.domChart_mem_maximalAtlas
    constructor
    · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
      exact (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m)).trans
        ((contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m)).symm hchi) hleft
    · have hright' : (e'.symm.trans h.domChart).trans chi ∈
          contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m) :=
        (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 m)).trans hright hchi
      simpa [e, OpenPartialHomeomorph.trans_assoc] using hright'
  · rw [Set.IsSliceInChart, Set.IsEuclideanSlice]
    refine ⟨Nat.sub_le m r, fun _ : Fin (m - (m - r)) ↦ (0 : ℝ), ?_⟩
    ext z
    constructor
    · rintro ⟨x, ⟨hxF, hxe⟩, rfl⟩
      refine ⟨e.map_source hxe, ?_⟩
      intro i
      have hxd : x ∈ h.domChart.source := by
        simpa [e, chi, OpenPartialHomeomorph.trans_source] using hxe
      have hnormal : rank_normal_form m n r (h.domChart x) = 0 := by
        calc
          rank_normal_form m n r (h.domChart x) = h.codChart (F x) := by
            simpa [Function.comp, h.domChart.left_inv hxd] using
              (h.eqOn (h.domChart.map_source hxd)).symm
          _ = h.codChart c := by simpa using congrArg h.codChart hxF
          _ = h.codChart (F p) := by rw [hpc]
          _ = 0 := h.codChart_centered.2
      let j : Fin r := Fin.cast (Nat.sub_sub_self hrm) i
      have hold : h.domChart x (Fin.castLE hrm j) = 0 := by
        have happ := constantRankNormalForm_apply_of_lt
          (m := m) (n := n) (r := r) (i := Fin.castLE hrn j)
          (by simpa using j.isLt) (by simpa using lt_of_lt_of_le j.isLt hrm)
          (h.domChart x)
        rw [hnormal] at happ
        have hidx :
            (⟨(Fin.castLE hrn j : Fin n).val,
              by simpa using lt_of_lt_of_le j.isLt hrm⟩ : Fin m) =
              Fin.castLE hrm j := by
          apply Fin.ext
          rfl
        rw [← hidx]
        exact happ.symm
      change constantRankFiberPerm m r hrm (h.domChart x)
          (Fin.cast (Nat.sub_add_cancel hrm) (Fin.natAdd (m - r) j)) = 0
      rw [constantRankFiberPerm_tail hrm (h.domChart x) j]
      exact hold
    · intro hz
      let x : M := e.symm z
      have hzTarget : z ∈ e.target := hz.1
      have hxSource : x ∈ e.source := e.symm.map_source hzTarget
      have hxd : x ∈ h.domChart.source := by
        simpa [x, e, chi, OpenPartialHomeomorph.trans_source] using hxSource
      have hex : e x = z := e.right_inv hzTarget
      have hold (j : Fin r) : h.domChart x (Fin.castLE hrm j) = 0 := by
        let i : Fin (m - (m - r)) := Fin.cast (Nat.sub_sub_self hrm).symm j
        have htail := hz.2 i
        rw [← hex] at htail
        change constantRankFiberPerm m r hrm (h.domChart x)
            (Fin.cast (Nat.sub_add_cancel hrm) (Fin.natAdd (m - r) j)) = 0 at htail
        rw [constantRankFiberPerm_tail hrm (h.domChart x) j] at htail
        exact htail
      have hnormal : rank_normal_form m n r (h.domChart x) = 0 := by
        ext q
        by_cases hqr : (q : ℕ) < r
        · have hqm : (q : ℕ) < m := lt_of_lt_of_le hqr hrm
          have happ := constantRankNormalForm_apply_of_lt
            (m := m) (n := n) (r := r) (i := q) hqr hqm (h.domChart x)
          rw [happ]
          let j : Fin r := ⟨q, hqr⟩
          have hj := hold j
          have hidx : (⟨(q : ℕ), hqm⟩ : Fin m) = Fin.castLE hrm j := by
            apply Fin.ext
            rfl
          rw [hidx]
          exact hj
        · simp [rank_normal_form, hqr]
      have hxF : F x = c := by
        have hFsource : F x ∈ h.codChart.source := h.mapsTo hxd
        have hcsource : c ∈ h.codChart.source := by
          rw [← hpc]
          exact h.codChart_centered.1
        apply h.codChart.injOn hFsource hcsource
        calc
          h.codChart (F x) = rank_normal_form m n r (h.domChart x) := by
            simpa [Function.comp, h.domChart.left_inv hxd] using
              h.eqOn (h.domChart.map_source hxd)
          _ = 0 := hnormal
          _ = h.codChart (F p) := h.codChart_centered.2.symm
          _ = h.codChart c := by rw [hpc]
      exact ⟨x, ⟨hxF, hxSource⟩, hex⟩

/-- Existential wrapper: an analytic regular-value chart yields an analytic slice chart. -/
theorem analytic_rankNormalForm_fiber_hasSliceChart
    {F : M → N} {p : M} {c : N}
    (h : AnalyticLocalCoordinateNormalFormAt F p (rank_normal_form m n n))
    (hpc : F p = c) (hnm : n ≤ m) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m)),
      p ∈ e.source ∧ e.IsSliceChart (F ⁻¹' {c}) (m - n) := by
  let e := h.domChart.trans
    (constantRankFiberPerm m n hnm).toHomeomorph.toOpenPartialHomeomorph
  refine ⟨e, ?_, ?_⟩
  · simpa [e, OpenPartialHomeomorph.trans_source] using h.domChart_centered.1
  · simpa using analytic_rankNormalForm_fiber_isSliceChart h hpc hnm le_rfl

end AnalyticOrthogonalFiberNormalForm

end
