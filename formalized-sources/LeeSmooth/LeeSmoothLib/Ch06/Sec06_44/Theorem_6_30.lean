import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16
import LeeSmoothLib.Ch05.Sec05_30.Definition_5_30_extra_3
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_38
import LeeSmoothLib.Ch06.Sec06_44.Theorem630_LevelSetOn
import LeeSmoothLib.Ch06.Sec06_44.Theorem630_SmoothModelTransport
import LeeSmoothLib.Verified.LevelSets.RegularValue

open scoped ContDiff Manifold
open Manifold Set Theorem630.SmoothModelTransport Theorem630.LevelSetOn
open TopologicalSpace

noncomputable section

set_option linter.unusedSectionVars false

/-!
# Theorem 6.30, genuine C∞ preimage and intersection

The original statement returned `IsEmbeddedSubmanifold`, whose inclusion field is outer-top
(`ω`, analytic).  A smooth map transverse to an analytic embedded submanifold need only cut out a
C∞ embedded preimage: the graph of the standard flat function
`x ↦ if x ≤ 0 then 0 else exp (-1 / x)` is a smooth embedded curve, not an analytic submanifold.
The corrected theorems therefore return the C∞ bundle
`ChartedSpace` + `IsManifold ∞` + `IsSmoothEmbedding ∞`.

Codimension arithmetic on an empty fibre is `Nat` subtraction, so the theorems assume
`codimension ≤ source dimension` rather than a nonempty fibre.  Nonemptiness still implies that
bound, by `transverse_codimension_le_source_finrank`.
-/

section TransversePreimage

universe uEN uEM uES uHN uHM uHS uN uM

variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HS : Type uHS} [TopologicalSpace HS]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {IN : ModelWithCorners ℝ EN HN} [IsManifold IN ∞ N]
variable {IM : ModelWithCorners ℝ EM HM} [IsManifold IM ∞ M]
variable {S : Set M}
variable {JS : ModelWithCorners ℝ ES HS}
variable [ChartedSpace HS S] [IsManifold JS ∞ S] [hS : IsEmbeddedSubmanifold IM JS S]

/-- If the transverse preimage is nonempty, then the target's codimension fits in the source
dimension. -/
lemma transverse_codimension_le_source_finrank
    {F : N → M} (htrans : IsTransverseToSubmanifold IM IN JS S F)
    (hTne : (F ⁻¹' S).Nonempty) :
    hS.codimension ≤ Module.finrank ℝ EN := by
  obtain ⟨p, hp⟩ := hTne
  let x : S := ⟨F p, hp⟩
  rcases immersionComplementCoordinates_levelSetOn (J := IM) (X := S) JS x with
    ⟨K, _, _, _, U, Φ, hpU, hDef, hdim⟩
  letI : NormedAddCommGroup (TangentSpace IN p) :=
    inferInstanceAs (NormedAddCommGroup EN)
  letI : NormedSpace ℝ (TangentSpace IN p) :=
    inferInstanceAs (NormedSpace ℝ EN)
  letI : FiniteDimensional ℝ (TangentSpace IN p) :=
    inferInstanceAs (FiniteDimensional ℝ EN)
  letI : NormedAddCommGroup (TangentSpace IM (F p)) :=
    inferInstanceAs (NormedAddCommGroup EM)
  letI : NormedSpace ℝ (TangentSpace IM (F p)) :=
    inferInstanceAs (NormedSpace ℝ EM)
  letI : FiniteDimensional ℝ (TangentSpace IM (F p)) :=
    inferInstanceAs (FiniteDimensional ℝ EM)
  letI : NormedAddCommGroup
      (TangentSpace (modelWithCornersSelf ℝ K) (Φ (F p))) :=
    inferInstanceAs (NormedAddCommGroup K)
  letI : NormedSpace ℝ
      (TangentSpace (modelWithCornersSelf ℝ K) (Φ (F p))) :=
    inferInstanceAs (NormedSpace ℝ K)
  letI : FiniteDimensional ℝ
      (TangentSpace (modelWithCornersSelf ℝ K) (Φ (F p))) :=
    inferInstanceAs (FiniteDimensional ℝ K)
  let A := mfderiv IN IM F p
  let B := mfderiv IM (modelWithCornersSelf ℝ K) Φ (F p)
  have hBsurj : Function.Surjective B := by
    simpa [B] using hDef.surjective_mfderiv hpU
  have hker : T[JS; x] = B.ker := by
    have hSubtype : Manifold.IsSmoothEmbedding JS IM ∞ (Subtype.val : S → M) :=
      isSmoothEmbedding_of_le (by simp) hS.isSmoothEmbedding_subtype_val
    simpa [B, x] using
      tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn
        hSubtype hDef hdim x hpU
  have htop : A.range ⊔ B.ker = ⊤ := by
    rw [← hker]
    simpa [A, x] using htrans.tangent_sup_eq_top ⟨p, hp⟩
  have hsurj : Function.Surjective (B.comp A) :=
    (surjectiveComp_iff_range_sup_ker_eq_top hBsurj).2 htop
  have hrank : Module.finrank ℝ K ≤ Module.finrank ℝ EN := by
    have hrank' := LinearMap.finrank_le_finrank_of_surjective hsurj
    change Module.finrank ℝ K ≤ Module.finrank ℝ EN at hrank'
    exact hrank'
  have hcodim : hS.codimension = Module.finrank ℝ K := by
    simp only [IsEmbeddedSubmanifold.codimension]
    omega
  rw [hcodim]
  exact hrank

private theorem emptySet_isSmoothEmbedding {k : ℕ} :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) (∅ : Set N),
      ∃ hs : IsManifold (𝓡 k) ∞ (∅ : Set N),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) (∅ : Set N) := cs
        let _ : IsManifold (𝓡 k) ∞ (∅ : Set N) := hs
        IsSmoothEmbedding (𝓡 k) IN ∞ (Subtype.val : (∅ : Set N) → N) := by
  let cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) (∅ : Set N) :=
    ChartedSpace.empty _ _
  refine ⟨cs, ?_⟩
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) (∅ : Set N) := cs
  let hs : IsManifold (𝓡 k) ∞ (∅ : Set N) := inferInstance
  refine ⟨hs, ?_⟩
  let _ : IsManifold (𝓡 k) ∞ (∅ : Set N) := hs
  exact ⟨⟨PUnit, inferInstance, inferInstance, fun x ↦ False.elim x.2⟩,
    Topology.IsEmbedding.subtypeVal⟩

/-- Theorem 6.30 (1), C∞ form: a smooth map transverse to an embedded submanifold has preimage a
C∞ embedded submanifold of the same codimension, provided that codimension fits in the source
dimension. -/
theorem transverse_preimage_has_embedded_submanifold_structure
    [IN.Boundaryless] [T2Space N] [SecondCountableTopology N]
    {F : N → M} (htrans : IsTransverseToSubmanifold IM IN JS S F)
    (hcod : hS.codimension ≤ Module.finrank ℝ EN) :
    let T : Set N := F ⁻¹' S
    let L :=
      modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ EN - hS.codimension)))
    ∃ cs : ChartedSpace
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ EN - hS.codimension))) T,
      ∃ hs : IsManifold L ∞ T,
        let _ : ChartedSpace
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ EN - hS.codimension))) T := cs
        let _ : IsManifold L ∞ T := hs
        IsSmoothEmbedding L IN ∞ (Subtype.val : T → N) := by
  dsimp only
  by_cases hEmpty : (F ⁻¹' S) = (∅ : Set N)
  · rw [hEmpty]
    exact emptySet_isSmoothEmbedding
  have hFsmooth : ContMDiff IN IM ∞ F := htrans.contMDiff
  let m : ℕ := Module.finrank ℝ EN
  let n : ℕ := hS.codimension
  have hnm : n ≤ m := hcod
  let b : Module.Basis (Fin m) ℝ EN := Module.finBasis ℝ EN
  let csN : ChartedSpace (EuclideanSpace ℝ (Fin m)) N :=
    euclideanChartedSpace (I := IN) rfl b
  letI : ChartedSpace (EuclideanSpace ℝ (Fin m)) N := csN
  letI : IsManifold (𝓡 m) ∞ N :=
    euclideanIsManifold (I := IN) rfl b
  have hForward : IsSmoothEmbedding (𝓡 m) IN ∞ (id : N → N) :=
    euclideanAmbientId_isSmoothEmbedding (I := IN) rfl b
  have hForwardLocal : IsLocalDiffeomorph (𝓡 m) IN ∞ (id : N → N) :=
    hForward.isImmersion.isLocalDiffeomorph_of_eq_finrank (by simp [m])
  have hLocal :
      ∀ p ∈ (F ⁻¹' S),
        ∃ U : Opens N, p ∈ U ∧
          ∃ Φ : U → EuclideanSpace ℝ (Fin n),
            Nonempty (Set.IsLocalDefiningMapOn (𝓡 m) (𝓡 n) (F ⁻¹' S) U Φ) := by
    intro p hp
    let x : S := ⟨F p, hp⟩
    rcases immersionComplementCoordinates_levelSetOn (J := IM) (X := S) JS x with
      ⟨K, _, _, _, U, Φ, hpU, hDef, hdimLocal⟩
    have hcodK : Module.finrank ℝ K = n := by
      simp only [n, IsEmbeddedSubmanifold.codimension]
      omega
    let eK : K ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp [hcodK])
    let V : Opens N :=
      ⟨F ⁻¹' U, hDef.isOpen_source.preimage hFsmooth.continuous⟩
    let g : V → K := fun y ↦ Φ (F y.1)
    let gE : V → EuclideanSpace ℝ (Fin n) := fun y ↦ eK (g y)
    refine ⟨V, hpU, gE, ⟨?_⟩⟩
    refine
      { level := eK (Φ (F p))
        contMDiff := ?_
        isLevelSet := ?_
        surj_mfderiv := ?_ }
    · have hIncl : ContMDiff (𝓡 m) IN ∞ (Subtype.val : V → N) := by
        have hOpen : ContMDiff (𝓡 m) (𝓡 m) ∞ (Subtype.val : V → N) :=
          contMDiff_subtype_val
        simpa [Function.comp] using hForward.contMDiff.comp hOpen
      have hFRestrict : ContMDiff (𝓡 m) IM ∞ (fun y : V ↦ F y.1) := by
        change ContMDiff (𝓡 m) IM ∞ (F ∘ (Subtype.val : V → N))
        exact hFsmooth.comp hIncl
      have hg : ContMDiff (𝓡 m) (modelWithCornersSelf ℝ K) ∞ g := by
        intro y
        have hΦAt : ContMDiffAt IM (modelWithCornersSelf ℝ K) ∞ Φ (F y.1) :=
          (hDef.smoothOn (F y.1) y.2).contMDiffAt
            (hDef.isOpen_source.mem_nhds y.2)
        exact hΦAt.comp y hFRestrict.contMDiffAt
      have heK :
          ContMDiff (modelWithCornersSelf ℝ K) (𝓡 n) ∞
            (eK : K → EuclideanSpace ℝ (Fin n)) :=
        eK.toContinuousLinearMap.contMDiff
      exact heK.comp hg
    · ext y
      constructor
      · intro hy
        change eK (Φ (F y.1)) = eK (Φ (F p))
        exact congrArg eK ((hDef.mem_iff_eq hp hpU y.2).1 hy)
      · intro hy
        have hyΦ : Φ (F y.1) = Φ (F p) := eK.injective hy
        exact (hDef.mem_iff_eq hp hpU y.2).2 hyΦ
    · intro y hy
      let xy : S := ⟨F y.1, hy⟩
      let A := mfderiv IN IM F y.1
      let B := mfderiv IM (modelWithCornersSelf ℝ K) Φ (F y.1)
      letI : NormedAddCommGroup (TangentSpace IN y.1) :=
        inferInstanceAs (NormedAddCommGroup EN)
      letI : NormedSpace ℝ (TangentSpace IN y.1) :=
        inferInstanceAs (NormedSpace ℝ EN)
      letI : NormedAddCommGroup (TangentSpace IM (F y.1)) :=
        inferInstanceAs (NormedAddCommGroup EM)
      letI : NormedSpace ℝ (TangentSpace IM (F y.1)) :=
        inferInstanceAs (NormedSpace ℝ EM)
      letI : NormedAddCommGroup
          (TangentSpace (modelWithCornersSelf ℝ K) (Φ (F y.1))) :=
        inferInstanceAs (NormedAddCommGroup K)
      letI : NormedSpace ℝ
          (TangentSpace (modelWithCornersSelf ℝ K) (Φ (F y.1))) :=
        inferInstanceAs (NormedSpace ℝ K)
      have hBsurj : Function.Surjective B := by
        simpa [B] using hDef.surjective_mfderiv y.2
      have hker : T[JS; xy] = B.ker := by
        have hSubtype : Manifold.IsSmoothEmbedding JS IM ∞
            (Subtype.val : S → M) :=
          isSmoothEmbedding_of_le (by simp) hS.isSmoothEmbedding_subtype_val
        simpa [B, xy] using
          tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn
            hSubtype hDef hdimLocal xy y.2
      have htop : A.range ⊔ B.ker = ⊤ := by
        rw [← hker]
        simpa [A, xy] using htrans.tangent_sup_eq_top ⟨y.1, hy⟩
      have hsurjBA : Function.Surjective (B.comp A) :=
        (surjectiveComp_iff_range_sup_ker_eq_top hBsurj).2 htop
      have hOpenLocal : IsLocalDiffeomorph (𝓡 m) (𝓡 m) ∞
          (Subtype.val : V → N) :=
        (Manifold.IsSmoothEmbedding.of_opens V).isImmersion
          |>.isLocalDiffeomorph_of_eq_finrank rfl
      have hInclLocal : IsLocalDiffeomorphAt (𝓡 m) IN ∞
          (Subtype.val : V → N) y := by
        simpa [Function.comp] using
          (hOpenLocal y).comp IN N (hForwardLocal y.1)
      have hInclSurj : Function.Surjective
          (mfderiv (𝓡 m) IN (Subtype.val : V → N) y) :=
        (hInclLocal.mfderivToContinuousLinearEquiv (by simp)).surjective
      have hΦAt : MDifferentiableAt IM (modelWithCornersSelf ℝ K) Φ (F y.1) :=
        ((hDef.smoothOn (F y.1) y.2).contMDiffAt
          (hDef.isOpen_source.mem_nhds y.2)).mdifferentiableAt (by simp)
      have hFAt : MDifferentiableAt IN IM F y.1 :=
        hFsmooth.mdifferentiableAt (by simp)
      have hIncl : ContMDiff (𝓡 m) IN ∞ (Subtype.val : V → N) := by
        have hOpen : ContMDiff (𝓡 m) (𝓡 m) ∞ (Subtype.val : V → N) :=
          contMDiff_subtype_val
        simpa [Function.comp] using hForward.contMDiff.comp hOpen
      have hInclAt : MDifferentiableAt (𝓡 m) IN (Subtype.val : V → N) y :=
        hIncl.mdifferentiableAt (by simp)
      have hFRestrict : ContMDiff (𝓡 m) IM ∞ (fun z : V ↦ F z.1) := by
        change ContMDiff (𝓡 m) IM ∞ (F ∘ (Subtype.val : V → N))
        exact hFsmooth.comp hIncl
      have hg : ContMDiff (𝓡 m) (modelWithCornersSelf ℝ K) ∞ g := by
        intro z
        have hΦAt' : ContMDiffAt IM (modelWithCornersSelf ℝ K) ∞ Φ (F z.1) :=
          (hDef.smoothOn (F z.1) z.2).contMDiffAt
            (hDef.isOpen_source.mem_nhds z.2)
        exact hΦAt'.comp z hFRestrict.contMDiffAt
      have hderiv_g :
          mfderiv (𝓡 m) (modelWithCornersSelf ℝ K) g y =
            (B.comp A).comp
              (mfderiv (𝓡 m) IN (Subtype.val : V → N) y) := by
        change mfderiv (𝓡 m) (modelWithCornersSelf ℝ K)
            (Φ ∘ (F ∘ (Subtype.val : V → N))) y = _
        rw [mfderiv_comp y hΦAt (hFAt.comp y hInclAt),
          mfderiv_comp y hFAt hInclAt]
        rfl
      have heKdiff :
          MDifferentiableAt (modelWithCornersSelf ℝ K) (𝓡 n)
            (eK : K → EuclideanSpace ℝ (Fin n)) (g y) :=
        eK.toContinuousLinearMap.contMDiff.mdifferentiableAt
          (by simp : (∞ : ℕ∞ω) ≠ 0)
      have hg_surj :
          Function.Surjective
            (mfderiv (𝓡 m) (modelWithCornersSelf ℝ K) g y) := by
        rw [hderiv_g]
        exact hsurjBA.comp hInclSurj
      have heK_surj :
          Function.Surjective
            (mfderiv (modelWithCornersSelf ℝ K) (𝓡 n)
              (eK : K → EuclideanSpace ℝ (Fin n)) (g y)) := by
        rw [mfderiv_eq_fderiv]
        change Function.Surjective
          (fderiv ℝ (eK.toContinuousLinearMap : K → EuclideanSpace ℝ (Fin n)) (g y))
        rw [eK.toContinuousLinearMap.fderiv]
        exact eK.surjective
      have hchain :
          mfderiv (𝓡 m) (𝓡 n) gE y =
            (mfderiv (modelWithCornersSelf ℝ K) (𝓡 n)
                (eK : K → EuclideanSpace ℝ (Fin n)) (g y)).comp
              (mfderiv (𝓡 m) (modelWithCornersSelf ℝ K) g y) := by
        change mfderiv (𝓡 m) (𝓡 n) (eK ∘ g) y = _
        exact mfderiv_comp y heKdiff
          (hg.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
      rw [hchain]
      exact heK_surj.comp hg_surj
  rcases LeeVerifiedLevelSets.LocalRegularLevelSmooth.local_regular_level_set_has_smooth_embedded_structure
      (F ⁻¹' S) hnm hLocal with ⟨cs, hs, hEmb⟩
  refine ⟨cs, ?_⟩
  refine ⟨hs, ?_⟩
  letI : ChartedSpace
      (EuclideanSpace ℝ (Fin (m - n))) (F ⁻¹' S) := cs
  letI : IsManifold (𝓡 (m - n)) ∞ (F ⁻¹' S) := hs
  simpa [Function.comp, m, n] using
    IsSmoothEmbedding.comp hForward hEmb

end TransversePreimage

section SmoothEmbeddingRange

universe uE₀ uE₁ uH₀ uH₁ uX uY

variable {E₀ : Type uE₀} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {H₀ : Type uH₀} [TopologicalSpace H₀]
variable {H₁ : Type uH₁} [TopologicalSpace H₁]
variable {X : Type uX} [TopologicalSpace X] [ChartedSpace H₀ X]
variable {Y : Type uY} [TopologicalSpace Y] [ChartedSpace H₁ Y]
variable {I₀ : ModelWithCorners ℝ E₀ H₀} [IsManifold I₀ ∞ X]
variable {I₁ : ModelWithCorners ℝ E₁ H₁}

private noncomputable abbrev theorem630TransportedRangeChartedSpace {f : X → Y}
    (e : X ≃ₜ Set.range f) : ChartedSpace H₀ (Set.range f) := by
  let _ : ChartedSpace X (Set.range f) :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  exact ChartedSpace.comp H₀ X (Set.range f)

private lemma theorem630TransportedRangeIsManifold {f : X → Y}
    (e : X ≃ₜ Set.range f) :
    let _ : ChartedSpace H₀ (Set.range f) := theorem630TransportedRangeChartedSpace e
    IsManifold I₀ ∞ (Set.range f) := by
  let eS : OpenPartialHomeomorph (Set.range f) X := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace X (Set.range f) := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace H₀ (Set.range f) := theorem630TransportedRangeChartedSpace e
  have hGroupoid : HasGroupoid (Set.range f) (contDiffGroupoid ∞ I₀) := by
    refine ⟨?_⟩
    rintro _ _ ⟨g, hg, c, hc, rfl⟩ ⟨g', hg', c', hc', rfl⟩
    have hgEq : g = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) g hg
    have hg'Eq : g' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) g' hg'
    subst g
    subst g'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl X := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈ contDiffGroupoid ∞ I₀ := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible (G := contDiffGroupoid ∞ I₀) hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  exact IsManifold.mk' I₀ ∞ (Set.range f)

private theorem theorem630SmoothEmbeddingRange {f : X → Y}
    (hf : Manifold.IsSmoothEmbedding I₀ I₁ ∞ f) :
    ∃ cs : ChartedSpace H₀ (Set.range f),
      ∃ hs : IsManifold I₀ ∞ (Set.range f),
        let _ : ChartedSpace H₀ (Set.range f) := cs
        let _ : IsManifold I₀ ∞ (Set.range f) := hs
        Manifold.IsSmoothEmbedding I₀ I₁ ∞
          (Subtype.val : Set.range f → Y) := by
  let e : X ≃ₜ Set.range f := hf.isEmbedding.toHomeomorph
  let cs : ChartedSpace H₀ (Set.range f) :=
    theorem630TransportedRangeChartedSpace e
  let _ : ChartedSpace H₀ (Set.range f) := cs
  have hs : IsManifold I₀ ∞ (Set.range f) :=
    theorem630TransportedRangeIsManifold e
  let _ : IsManifold I₀ ∞ (Set.range f) := hs
  have hSubtypeImmersion : Manifold.IsImmersion I₀ I₁ ∞
      (Subtype.val : Set.range f → Y) := by
    let hImm := hf.isImmersion
    let hComp := hImm.complement
    let hCompImm := hImm.isImmersionOfComplement_complement
    let eS : OpenPartialHomeomorph (Set.range f) X := e.symm.toOpenPartialHomeomorph
    let _ : ChartedSpace X (Set.range f) := eS.singletonChartedSpace (by
      ext z
      simp [eS])
    refine ⟨hComp, inferInstance, inferInstance, ?_⟩
    intro x
    let hx := hCompImm (e.symm x)
    refine Manifold.IsImmersionAtOfComplement.mk_of_charts
      hx.equiv (e.symm.toOpenPartialHomeomorph.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
    · have hxe : f (e.symm x) = (x : Y) := by
        exact congrArg Subtype.val (e.apply_symm_apply x)
      simpa [hxe] using hx.mem_codChart_source
    · intro d hd
      rcases hd with ⟨g, hg, c', hc', rfl⟩
      have hgEq : g = eS := by
        simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
          ext z
          simp [eS]) g hg
      subst g
      have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl X := by
        simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
      constructor
      · have hleft :
            ((hx.domChart.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
              contDiffGroupoid ∞ I₀ := by
          rw [hmid, OpenPartialHomeomorph.trans_refl]
          exact (hx.domChart_mem_maximalAtlas c' hc').1
        simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc] using hleft
      · have hright :
            ((c'.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ hx.domChart) ∈
              contDiffGroupoid ∞ I₀ := by
          rw [hmid, OpenPartialHomeomorph.trans_refl]
          exact (hx.domChart_mem_maximalAtlas c' hc').2
        simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc] using hright
    · exact hx.codChart_mem_maximalAtlas
    · intro z hz
      have hz' : e.symm z ∈ hx.domChart.source := by
        simpa [OpenPartialHomeomorph.trans_source] using hz
      have hze : f (e.symm z) = (z : Y) := by
        exact congrArg Subtype.val (e.apply_symm_apply z)
      simpa [hze] using hx.source_subset_preimage_source hz'
    · intro u hu
      have hu' : u ∈ (hx.domChart.extend I₀).target := by
        simpa [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
      simpa [Function.comp, OpenPartialHomeomorph.extend_coe_symm,
        OpenPartialHomeomorph.extend_coe] using! hx.writtenInCharts hu'
  exact ⟨cs, hs, ⟨hSubtypeImmersion, Topology.IsEmbedding.subtypeVal⟩⟩

end SmoothEmbeddingRange

section TransverseIntersection

universe uEM uES uES' uHM uHS uHS' uM

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
variable {ES' : Type uES'} [NormedAddCommGroup ES'] [NormedSpace ℝ ES']
  [FiniteDimensional ℝ ES']
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HS : Type uHS} [TopologicalSpace HS]
variable {HS' : Type uHS'} [TopologicalSpace HS']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {IM : ModelWithCorners ℝ EM HM} [IsManifold IM ∞ M]
variable {S : Set M} {S' : Set M}
variable {JS : ModelWithCorners ℝ ES HS} {JS' : ModelWithCorners ℝ ES' HS'}
variable [ChartedSpace HS S] [IsManifold JS ∞ S] [hS : IsEmbeddedSubmanifold IM JS S]
variable [ChartedSpace HS' S'] [IsManifold JS' ∞ S'] [hS' : IsEmbeddedSubmanifold IM JS' S']

/-- Theorem 6.30 (2), C∞ form: a transverse intersection of embedded submanifolds is a C∞
embedded submanifold whose codimension is the sum of the two codimensions, provided that sum
fits in the ambient dimension. -/
theorem transverse_intersection_has_embedded_submanifold_structure
    [JS.Boundaryless] [IM.Boundaryless] [T2Space M] [SecondCountableTopology M]
    (htrans : SubmanifoldsIntersectTransversely IM JS S JS' S')
    (hcod : hS.codimension + hS'.codimension ≤ Module.finrank ℝ EM) :
    let T : Set M := S ∩ S'
    let L :=
      modelWithCornersSelf ℝ
        (EuclideanSpace ℝ
          (Fin (Module.finrank ℝ EM - (hS.codimension + hS'.codimension))))
    ∃ cs : ChartedSpace
        (EuclideanSpace ℝ
          (Fin (Module.finrank ℝ EM - (hS.codimension + hS'.codimension)))) T,
      ∃ hs : IsManifold L ∞ T,
        let _ : ChartedSpace
            (EuclideanSpace ℝ
              (Fin (Module.finrank ℝ EM - (hS.codimension + hS'.codimension)))) T := cs
        let _ : IsManifold L ∞ T := hs
        IsSmoothEmbedding L IM ∞ (Subtype.val : T → M) := by
  dsimp only
  by_cases hEmpty : (S ∩ S') = (∅ : Set M)
  · rw [hEmpty]
    exact emptySet_isSmoothEmbedding (k := Module.finrank ℝ EM -
      (hS.codimension + hS'.codimension)) (IN := IM)
  have hTne : (S ∩ S').Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
  letI : BoundarylessManifold JS S := hS.toBoundarylessManifold
  letI : T2Space S := hS.isSmoothEmbedding_subtype_val.isEmbedding.t2Space
  letI : SecondCountableTopology S :=
    hS.isSmoothEmbedding_subtype_val.isEmbedding.secondCountableTopology
  let f : S → M := Subtype.val
  have hftrans : IsTransverseToSubmanifold IM JS JS' S' f :=
    (submanifoldsIntersectTransversely_iff_left_inclusion_transverse).1 htrans
  have hSne : S.Nonempty := by
    obtain ⟨p, hpS, _⟩ := hTne
    exact ⟨p, hpS⟩
  have hESle : Module.finrank ℝ ES ≤ Module.finrank ℝ EM := by
    obtain ⟨p, hpS⟩ := hSne
    have hEmb : IsSmoothEmbedding JS IM ∞ (Subtype.val : S → M) :=
      isSmoothEmbedding_of_le (by simp) hS.isSmoothEmbedding_subtype_val
    let hp := hEmb.isImmersion.isImmersionAt ⟨p, hpS⟩
    haveI : FiniteDimensional ℝ (ES × hp.complement) :=
      FiniteDimensional.of_injective hp.equiv.toLinearMap hp.equiv.injective
    have hinj : Function.Injective
        (hp.equiv.toLinearMap.comp (LinearMap.inl ℝ ES hp.complement)) :=
      hp.equiv.injective.comp LinearMap.inl_injective
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using hle
  have hcod' : hS'.codimension ≤ Module.finrank ℝ ES := by
    simp only [IsEmbeddedSubmanifold.codimension] at hcod ⊢
    omega
  have hw := transverse_preimage_has_embedded_submanifold_structure
    (IM := IM) (IN := JS) (JS := JS') (S := S') hftrans hcod'
  dsimp only at hw
  rcases hw with ⟨csW, hsW, hW⟩
  letI : ChartedSpace
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ ES - hS'.codimension)))
      (f ⁻¹' S') := csW
  letI : IsManifold
      (𝓡 (Module.finrank ℝ ES - hS'.codimension)) ∞ (f ⁻¹' S') := hsW
  let j : (f ⁻¹' S') → M :=
    (Subtype.val : S → M) ∘ (Subtype.val : (f ⁻¹' S') → S)
  have hj : Manifold.IsSmoothEmbedding
      (𝓡 (Module.finrank ℝ ES - hS'.codimension)) IM ∞ j := by
    have hSemb : IsSmoothEmbedding JS IM ∞ (Subtype.val : S → M) :=
      isSmoothEmbedding_of_le (by simp) hS.isSmoothEmbedding_subtype_val
    exact IsSmoothEmbedding.comp hSemb hW
  have hrange : Set.range j = S ∩ S' := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1.2, q.2⟩
    · rintro ⟨hpS, hpS'⟩
      exact ⟨⟨⟨p, hpS⟩, hpS'⟩, rfl⟩
  have hdim :
      Module.finrank ℝ ES - hS'.codimension =
        Module.finrank ℝ EM - (hS.codimension + hS'.codimension) := by
    simp only [IsEmbeddedSubmanifold.codimension]
    omega
  rcases theorem630SmoothEmbeddingRange hj with ⟨csR₀, hsR₀, hR₀⟩
  have hRangePack :
      ∃ csR : ChartedSpace
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ ES - hS'.codimension))) ↑(S ∩ S'),
        ∃ hsR : IsManifold (𝓡 (Module.finrank ℝ ES - hS'.codimension)) ∞ ↑(S ∩ S'),
          let _ : ChartedSpace
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ ES - hS'.codimension)))
              ↑(S ∩ S') := csR
          let _ : IsManifold (𝓡 (Module.finrank ℝ ES - hS'.codimension)) ∞
              ↑(S ∩ S') := hsR
          Manifold.IsSmoothEmbedding
            (𝓡 (Module.finrank ℝ ES - hS'.codimension)) IM ∞
            (Subtype.val : ↑(S ∩ S') → M) := by
    rw [← hrange]
    exact ⟨csR₀, hsR₀, hR₀⟩
  rcases hRangePack with ⟨csR, hsR, hR⟩
  rw [← hdim]
  exact ⟨csR, hsR, hR⟩

end TransverseIntersection
