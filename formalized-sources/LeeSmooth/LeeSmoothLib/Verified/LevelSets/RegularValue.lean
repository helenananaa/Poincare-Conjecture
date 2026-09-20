import Mathlib
import LeeSmoothLib.Ch05.Sec05_30.RegularValueLocalNormalForm
import LeeSmoothLib.Verified.LevelSets.ConstantRank
import LeeSmoothLib.Ch05.Sec05_30.Definition_5_30_extra_3
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3

open scoped ContDiff Manifold

noncomputable section

namespace LeeVerifiedLevelSets

section RegularLevelSetStructure

open Manifold

/-- Corollary 5.14 (1), with the honest `C∞` bundled conclusion.

The local charts are constructed directly from the surjective derivative: choose a linear
complement, apply the inverse function theorem, turn the resulting projection normal form into a
slice chart, and glue the slice atlas.  In particular there is no analytic normal-form hypothesis.
The explicit bound `n ≤ m` fixes the dimension convention even for an empty fiber.

We deliberately do not return the repository's older `IsEmbeddedSubmanifold`, whose inclusion
field is outer-top (`ω`, analytic).  A standard counterexample to any smooth-to-analytic shortcut
is the graph of `x ↦ if x ≤ 0 then 0 else exp (-1 / x)`: it is `C∞` but nonanalytic at zero. -/
theorem regular_level_set_has_embedded_submanifold_structure
    {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [IsManifold (𝓡 m) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    {Φ : M → N} {c : N}
    (hΦ : ContMDiff (𝓡 m) (𝓡 n) ∞ Φ)
    (hc : IsRegularValue (𝓡 m) (𝓡 n) Φ c)
    (hnm : n ≤ m) :
    let k : ℕ := m - n
    let S : Set M := Φ ⁻¹' {c}
    let K := 𝓡 k
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
        ∃ hs : IsManifold K ∞ S,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
        let _ : IsManifold K ∞ S := hs
        IsSmoothEmbedding K (𝓡 m) ∞ (Subtype.val : S → M) := by
  dsimp
  let S : Set M := Φ ⁻¹' {c}
  let _ : TopologicalManifold m M := topologicalManifoldOfChartedSpace m M
  have hSlice : Set.SatisfiesLocalSmoothSliceCondition m S (m - n) := by
    refine ⟨?_⟩
    intro p hp
    have hpc : Φ p = c := Set.mem_singleton_iff.mp hp
    rcases RegularValueLocalNormalForm.at_of_surjective_mfderiv hΦ p (hc p hpc) with ⟨h, _⟩
    exact smooth_rankNormalForm_fiber_hasSliceChart h hpc hnm le_rfl
  exact LevelSetSmoothSlice.local_smooth_slice_condition_has_smooth_embedded_structure S hSlice

namespace LocalRegularLevelSmooth

/-- The inverse chart of the inclusion of an open subtype is smooth on its natural source. -/
private theorem openSubtypeCoe_symm_contMDiffOn
    {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [IsManifold (𝓡 m) ∞ M]
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    let iU := U.openPartialHomeomorphSubtypeCoe hU
    ContMDiffOn (𝓡 m) (𝓡 m) ∞ iU.symm (U : Set M) := by
  dsimp only
  let iU := U.openPartialHomeomorphSubtypeCoe hU
  intro x hx
  have hcomp :
      ContMDiffWithinAt (𝓡 m) (𝓡 m) ∞ (Subtype.val ∘ iU.symm) (U : Set M) x := by
    refine contMDiffWithinAt_id.congr_of_mem ?_ hx
    intro y hy
    have hyTarget : y ∈ iU.target := by
      simpa [iU, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hy
    simpa [iU, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
      iU.right_inv hyTarget
  have hiff :
      ChartedSpace.LiftPropWithinAt (ContDiffWithinAtProp (𝓡 m) (𝓡 m) ∞)
          (Subtype.val ∘ iU.symm) (U : Set M) x ↔
        ChartedSpace.LiftPropWithinAt (ContDiffWithinAtProp (𝓡 m) (𝓡 m) ∞)
          iU.symm (U : Set M) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff iU.symm (U : Set M) x
  simpa [ContMDiffWithinAt] using hiff.mp (by simpa [ContMDiffWithinAt] using hcomp)

/-- A smooth slice chart on an open subtype is canonically an ambient smooth slice chart.
This is the locality bridge needed to glue independently supplied local defining maps. -/
theorem ambientSliceChart_of_openSubtype
    {m k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [IsManifold (𝓡 m) ∞ M]
    (S : Set M) (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (e : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin m)))
    (he : e.IsSmoothSliceChart {x : U | (x : M) ∈ S} k) :
    ∃ eM : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m)),
      eM.IsSmoothSliceChart S k ∧
        ∀ x : U, x ∈ e.source → (x : M) ∈ eM.source := by
  let iU := U.openPartialHomeomorphSubtypeCoe hU
  let eM := iU.symm.trans e
  have hiInv (x : M) (hx : x ∈ U) : (iU.symm x : U) = ⟨x, hx⟩ := by
    apply Subtype.ext
    have hxTarget : x ∈ iU.target := by
      simpa [iU, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hx
    simpa [iU, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
      iU.right_inv hxTarget
  have hmax : eM ∈ IsManifold.maximalAtlas (𝓡 m) ∞ M := by
    apply eM.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn (𝓡 m) (𝓡 m) ∞ (iU.symm.trans e) (iU.symm.trans e).source
      rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source]
      have hiSmooth : ContMDiffOn (𝓡 m) (𝓡 m) ∞ iU.symm iU.symm.source := by
        simpa [iU, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using
          (openSubtypeCoe_symm_contMDiffOn (m := m) U hU)
      exact (contMDiffOn_of_mem_maximalAtlas he.1).comp'
        hiSmooth
    · change ContMDiffOn (𝓡 m) (𝓡 m) ∞ (iU.symm.trans e).symm
        (iU.symm.trans e).target
      rw [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.trans_target]
      have hval : ContMDiff (𝓡 m) (𝓡 m) ∞ (Subtype.val : U → M) :=
        contMDiff_subtype_val
      simpa [eM, iU, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
          hval.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he.1)
  have htarget : eM.target = e.target := by
    simp [eM, iU, OpenPartialHomeomorph.trans_target,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source]
  have himage :
      eM '' (S ∩ eM.source) = e '' ({x : U | (x : M) ∈ S} ∩ e.source) := by
    ext z
    constructor
    · rintro ⟨x, ⟨hxS, hxSource⟩, rfl⟩
      have hxU : x ∈ U := by
        have := hxSource.1
        simpa [eM, iU, OpenPartialHomeomorph.trans_source,
          TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using this
      have hxe : (⟨x, hxU⟩ : U) ∈ e.source := by
        have := hxSource.2
        simpa [hiInv x hxU] using this
      refine ⟨(⟨x, hxU⟩ : U), ⟨hxS, hxe⟩, ?_⟩
      change e ⟨x, hxU⟩ = e (iU.symm x)
      rw [hiInv x hxU]
    · rintro ⟨x, ⟨hxS, hxe⟩, rfl⟩
      refine ⟨(x : M), ⟨hxS, ?_⟩, ?_⟩
      · simp only [eM, OpenPartialHomeomorph.trans_source]
        constructor
        · simpa [iU, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using x.2
        · simpa [hiInv x x.2] using hxe
      · change e (iU.symm (x : M)) = e x
        rw [hiInv x x.2]
  have hslice : S.IsSliceInChart eM k := by
    have heSlice := he.2
    rw [Set.IsSliceInChart, Set.IsEuclideanSlice] at heSlice ⊢
    rcases heSlice with ⟨hk, c, hc⟩
    refine ⟨hk, c, ?_⟩
    rw [himage, htarget, hc]
  refine ⟨eM, ⟨hmax, hslice⟩, ?_⟩
  intro x hx
  simp only [eM, OpenPartialHomeomorph.trans_source]
  constructor
  · simpa [iU, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using x.2
  · simpa [hiInv x x.2] using hx

/-- A reusable `C∞` local-regular-level theorem.  Local defining maps may live on unrelated open
neighborhoods; each one supplies a direct IFT slice chart on its open subtype, which is promoted to
an ambient chart and then glued by the smooth local-slice atlas. -/
theorem local_regular_level_set_has_smooth_embedded_structure
    {m n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [IsManifold (𝓡 m) ∞ M]
    (S : Set M) (hnm : n ≤ m)
    (hLocal :
      ∀ p ∈ S,
        ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
          ∃ Φ : U → EuclideanSpace ℝ (Fin n),
            Nonempty (Set.IsLocalDefiningMapOn (𝓡 m) (𝓡 n) S U Φ)) :
    let k := m - n
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
      ∃ hs : IsManifold (𝓡 k) ∞ S,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
        let _ : IsManifold (𝓡 k) ∞ S := hs
        IsSmoothEmbedding (𝓡 k) (𝓡 m) ∞ (Subtype.val : S → M) := by
  dsimp
  let _ : TopologicalManifold m M := topologicalManifoldOfChartedSpace m M
  have hSlice : Set.SatisfiesLocalSmoothSliceCondition m S (m - n) := by
    refine ⟨?_⟩
    intro p hp
    rcases hLocal p hp with ⟨U, hpU, Φ, ⟨hΦ⟩⟩
    let pU : U := ⟨p, hpU⟩
    have hpLevel : Φ pU = hΦ.level := by
      have hpFiber : pU ∈ Φ ⁻¹' {hΦ.level} := by
        rw [← hΦ.isLevelSet]
        exact hp
      exact Set.mem_singleton_iff.mp hpFiber
    rcases RegularValueLocalNormalForm.at_of_surjective_mfderiv
        hΦ.contMDiff pU (hΦ.surj_mfderiv pU hp) with ⟨hNormal, _⟩
    rcases smooth_rankNormalForm_fiber_hasSliceChart
        hNormal hpLevel hnm le_rfl with ⟨eU, hpEU, heU⟩
    have heUS : eU.IsSmoothSliceChart {x : U | (x : M) ∈ S} (m - n) := by
      rw [hΦ.isLevelSet]
      exact heU
    rcases ambientSliceChart_of_openSubtype S U ⟨pU⟩ eU heUS with
      ⟨eM, heM, hpromote⟩
    exact ⟨eM, hpromote pU hpEU, heM⟩
  exact LevelSetSmoothSlice.local_smooth_slice_condition_has_smooth_embedded_structure S hSlice

end LocalRegularLevelSmooth

end RegularLevelSetStructure

section ProperEmbedding

universe uE uE' uH uH' uM uN

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

/-- Corollary 5.14 (2): a smooth regular level set is closed, hence properly embedded as a
subset. -/
theorem regular_level_set_isProperlyEmbedded [T1Space N] {Φ : M → N} {c : N}
    (hΦ : ContMDiff I J ∞ Φ) (hc : IsRegularValue I J Φ c) :
    (Φ ⁻¹' {c}).IsProperlyEmbedded := by
  exact (isClosed_singleton.preimage hΦ.continuous).isProperlyEmbedded

end ProperEmbedding

end LeeVerifiedLevelSets
