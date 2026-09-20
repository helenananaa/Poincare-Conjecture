import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Normed.Module.Connected
import LeeSmoothLib.Ch04.Sec04_26.Proposition_4_40
import LeeSmoothLib.External.TauCeti.AlgebraicTopology.UniversalCover.Covering
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uMtilde uE' uH' uM'

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable [ConnectedSpace M]

/-- A charted space over a real or complex normed model is locally path connected. -/
private theorem corollary_4_43_locallyPathConnectedSpace
    {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [IsRCLikeNormedField 𝕜']
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜' ES]
    {HS : Type*} [TopologicalSpace HS] {J : ModelWithCorners 𝕜' ES HS}
    {S : Type*} [TopologicalSpace S] [ChartedSpace HS S] :
    LocallyPathConnectedSpace S := by
  letI : RCLike 𝕜' := IsRCLikeNormedField.rclike 𝕜'
  letI : NormedSpace ℝ ES := NormedSpace.restrictScalars ℝ 𝕜' ES
  letI : LocallyPathConnectedSpace (Set.range J) :=
    J.convex_range.locallyPathConnectedSpace
  let e : HS ≃ₜ Set.range J := J.isClosedEmbedding.toHomeomorph
  letI : LocallyPathConnectedSpace HS := e.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace HS S

private theorem corollary_4_43_convex_stronglyLocallyContractibleSpace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set F} (hs : Convex ℝ s) : StronglyLocallyContractibleSpace s := by
  refine StronglyLocallyContractibleSpace.of_bases
    (fun x : s ↦ Metric.nhds_basis_ball) ?_
  intro x r hr
  let e : (Metric.ball x r : Set s) ≃ₜ
      (Subtype.val '' (Metric.ball x r : Set s) : Set F) :=
    Topology.IsEmbedding.subtypeVal.homeomorphImage _
  apply e.contractibleSpace_iff.mpr
  rw [Subtype.image_ball]
  exact (convex_ball (x : F) r).inter hs |>.contractibleSpace
    ⟨x, Metric.mem_ball_self hr, x.property⟩

/-- A model-with-corners space is strongly locally contractible because it is homeomorphic to the
convex range of its model map. -/
private theorem corollary_4_43_model_stronglyLocallyContractibleSpace
    {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [IsRCLikeNormedField 𝕜']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F]
    {G : Type*} [TopologicalSpace G] (J : ModelWithCorners 𝕜' F G) :
    StronglyLocallyContractibleSpace G := by
  letI : RCLike 𝕜' := IsRCLikeNormedField.rclike 𝕜'
  letI : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜' F
  letI : StronglyLocallyContractibleSpace (Set.range J) :=
    corollary_4_43_convex_stronglyLocallyContractibleSpace J.convex_range
  let e : G ≃ₜ Set.range J := J.isClosedEmbedding.toHomeomorph
  exact e.isOpenEmbedding.stronglyLocallyContractibleSpace

/-- Strong local contractibility transfers from the model through a charted-space atlas. -/
private theorem corollary_4_43_charted_stronglyLocallyContractibleSpace
    {G S : Type*} [TopologicalSpace G] [StronglyLocallyContractibleSpace G]
    [TopologicalSpace S] [ChartedSpace G S] : StronglyLocallyContractibleSpace S := by
  let e : S → OpenPartialHomeomorph S G := chartAt G
  refine StronglyLocallyContractibleSpace.of_bases
    (p := fun x (s : Set G) ↦ (s ∈ nhds (e x x) ∧ ContractibleSpace s) ∧ s ⊆ (e x).target)
    (s := fun x (s : Set G) ↦ (e x).symm '' s) ?_ ?_
  · intro x
    simpa only [e, OpenPartialHomeomorph.symm_map_nhds_eq, mem_chart_source] using!
      ((contractible_basis (e x x)).restrict_subset
        ((e x).open_target.mem_nhds (mem_chart_target G x))).map (e x).symm
  · rintro x s ⟨hs, hstarget⟩
    let φ : s ≃ₜ ((e x).symm '' s) :=
      (e x).symm.homeomorphOfImageSubsetSource hstarget rfl
    exact φ.contractibleSpace_iff.mp hs.2

omit [IsManifold I ∞ M] [ConnectedSpace M] in
/-- Every charted space modelled on a real or complex model with corners is strongly locally
contractible.  In particular it is locally path connected and semilocally simply connected. -/
theorem corollary_4_43_stronglyLocallyContractibleSpace [IsRCLikeNormedField 𝕜]
    (I : ModelWithCorners 𝕜 E H) : StronglyLocallyContractibleSpace M := by
  letI : StronglyLocallyContractibleSpace H :=
    corollary_4_43_model_stronglyLocallyContractibleSpace I
  exact corollary_4_43_charted_stronglyLocallyContractibleSpace (G := H)

/-- A continuous map is smooth if its composite with a smooth local diffeomorphism is smooth. -/
private lemma corollary_4_43_contMDiff_of_comp_eq
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners 𝕜 E₀ H₀}
    {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners 𝕜 E₁ H₁}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners 𝕜 E₂ H₂}
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {f : M₀ → M₁} {g : M₁ → M₂} {h : M₀ → M₂}
    (hf : Continuous f) (hg : IsLocalDiffeomorph I₁ I₂ ∞ g)
    (hh : ContMDiff I₀ I₂ ∞ h) (hcomp : g ∘ f = h) :
    ContMDiff I₀ I₁ ∞ f := by
  intro x
  let hgx := hg (f x)
  have hcompx : g (f x) = h x := by
    simpa [Function.comp_apply] using congr_fun hcomp x
  have houter : ContMDiffAt I₂ I₁ ∞ hgx.localInverse (h x) := by
    simpa [hcompx] using hgx.localInverse_contMDiffAt
  have hlocal : hgx.localInverse ∘ h =ᶠ[nhds x] f := by
    have hleft : (hgx.localInverse ∘ g) ∘ f =ᶠ[nhds x] id ∘ f :=
      hgx.localInverse_eventuallyEq_left.comp_tendsto hf.continuousAt
    simpa [Function.comp_apply, Function.comp_assoc, hcomp] using hleft
  exact (houter.comp x (hh x)).congr_of_eventuallyEq hlocal.symm

omit [IsManifold I ∞ M] [ConnectedSpace M] in
/-- Any two universal smooth covering manifolds over the same base are diffeomorphic over it. -/
theorem exists_diffeomorph_of_universal_smooth_covering_maps
    [IsRCLikeNormedField 𝕜]
    {E₁ : Type uE'} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {H₁ : Type uH'} [TopologicalSpace H₁] {I₁ : ModelWithCorners 𝕜 E₁ H₁}
    {M₁ : Type uMtilde} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners 𝕜 E₂ H₂}
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    (π₁ : M₁ → M) (hπ₁ : Manifold.IsUniversalSmoothCoveringMap I₁ I π₁)
    (π₂ : M₂ → M) (hπ₂ : Manifold.IsUniversalSmoothCoveringMap I₂ I π₂) :
    ∃ Φ : Diffeomorph I₁ I₂ M₁ M₂ (∞ : WithTop ℕ∞), π₂ ∘ Φ = π₁ := by
  letI : SimplyConnectedSpace M₁ := hπ₁.simplyConnectedSpace
  letI : SimplyConnectedSpace M₂ := hπ₂.simplyConnectedSpace
  letI : LocallyPathConnectedSpace M₁ :=
    corollary_4_43_locallyPathConnectedSpace (J := I₁)
  letI : LocallyPathConnectedSpace M₂ :=
    corollary_4_43_locallyPathConnectedSpace (J := I₂)
  let x₀ : M₁ := Classical.arbitrary M₁
  obtain ⟨y₀, hy₀⟩ := hπ₂.isSmoothCoveringMap.surjective (π₁ x₀)
  let π₁c : C(M₁, M) :=
    ⟨π₁, hπ₁.isSmoothCoveringMap.isLocalDiffeomorph.contMDiff.continuous⟩
  obtain ⟨F, hF, -⟩ :=
    hπ₂.isSmoothCoveringMap.isCoveringMap.existsUnique_continuousMap_lifts
      π₁c x₀ y₀ hy₀
  let π₂c : C(M₂, M) :=
    ⟨π₂, hπ₂.isSmoothCoveringMap.isLocalDiffeomorph.contMDiff.continuous⟩
  obtain ⟨G, hG, -⟩ :=
    hπ₁.isSmoothCoveringMap.isCoveringMap.existsUnique_continuousMap_lifts
      π₂c y₀ x₀ hy₀.symm
  have hGF_comp : π₁ ∘ (G ∘ F) = π₁ := by
    funext x
    calc
      π₁ (G (F x)) = π₂ (F x) := by
        simpa [π₂c] using congr_fun hG.2 (F x)
      _ = π₁ x := by
        simpa [π₁c] using congr_fun hF.2 x
  have hFG_comp : π₂ ∘ (F ∘ G) = π₂ := by
    funext y
    calc
      π₂ (F (G y)) = π₁ (G y) := by
        simpa [π₁c] using congr_fun hF.2 (G y)
      _ = π₂ y := by
        simpa [π₂c] using congr_fun hG.2 y
  have hGF : (G : M₂ → M₁) ∘ F = id := by
    refine hπ₁.isSmoothCoveringMap.isCoveringMap.eq_of_comp_eq
      (G.continuous.comp F.continuous) continuous_id ?_ x₀ ?_
    · simpa [Function.comp_assoc] using hGF_comp
    · simp [Function.comp_apply, hF.1, hG.1]
  have hFG : (F : M₁ → M₂) ∘ G = id := by
    refine hπ₂.isSmoothCoveringMap.isCoveringMap.eq_of_comp_eq
      (F.continuous.comp G.continuous) continuous_id ?_ y₀ ?_
    · simpa [Function.comp_assoc] using hFG_comp
    · simp [Function.comp_apply, hF.1, hG.1]
  have hF_smooth : ContMDiff I₁ I₂ ∞ F := by
    refine corollary_4_43_contMDiff_of_comp_eq F.continuous
      hπ₂.isSmoothCoveringMap.isLocalDiffeomorph
      hπ₁.isSmoothCoveringMap.isLocalDiffeomorph.contMDiff ?_
    simpa [π₁c] using hF.2
  have hG_smooth : ContMDiff I₂ I₁ ∞ G := by
    refine corollary_4_43_contMDiff_of_comp_eq G.continuous
      hπ₁.isSmoothCoveringMap.isLocalDiffeomorph
      hπ₂.isSmoothCoveringMap.isLocalDiffeomorph.contMDiff ?_
    simpa [π₂c] using hG.2
  let e : M₁ ≃ M₂ :=
    { toFun := F
      invFun := G
      left_inv := fun x ↦ congr_fun hGF x
      right_inv := fun y ↦ congr_fun hFG y }
  refine ⟨{ toEquiv := e, contMDiff_toFun := hF_smooth, contMDiff_invFun := hG_smooth }, ?_⟩
  change π₂ ∘ (F : M₁ → M₂) = π₁
  simpa [π₁c] using hF.2

-- Proof sketch: use the topological existence theorem for universal covering spaces on connected
-- manifolds, transport the smooth atlas along the covering projection to make the universal cover a
-- smooth manifold, and then apply uniqueness of lifts between simply connected covers to upgrade
-- the comparison homeomorphism to a diffeomorphism over the base.
/-- Corollary 4.43: every connected smooth manifold admits a universal smooth covering map from a
simply connected smooth manifold, and any other simply connected smooth covering of the same base
is diffeomorphic to it over the base. -/
theorem exists_universal_smooth_covering_manifold [IsRCLikeNormedField 𝕜]
    : ∃ (Mtilde : Type uM) (_ : TopologicalSpace Mtilde) (_ : ChartedSpace H Mtilde)
      (_ : IsManifold I ∞ Mtilde) (π : Mtilde → M),
      Manifold.IsUniversalSmoothCoveringMap I I π ∧
        ∀ {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
          {H' : Type uH'} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
          {M' : Type uM'} [TopologicalSpace M'] [ChartedSpace H' M']
          [IsManifold I' ∞ M']
          (π' : M' → M),
          Manifold.IsUniversalSmoothCoveringMap I' I π' →
            ∃ Φ : Diffeomorph I I' Mtilde M' (∞ : WithTop ℕ∞), π' ∘ Φ = π := by
  letI : StronglyLocallyContractibleSpace M :=
    corollary_4_43_stronglyLocallyContractibleSpace (I := I)
  letI : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let x₀ : M := Classical.arbitrary M
  let Mtilde : Type uM := TauCeti.UniversalCover x₀
  let π : Mtilde → M := TauCeti.UniversalCover.proj
  have hcover : IsCoveringMap π := TauCeti.UniversalCover.isCoveringMap x₀
  have hsurj : Function.Surjective π := by
    intro x
    let p : Path x₀ x := PathConnectedSpace.somePath x₀ x
    refine ⟨TauCeti.UniversalCover.ofBasedPath x₀ (BasedPath.ofPath p), ?_⟩
    simpa [π] using
      (TauCeti.UniversalCover.proj_ofBasedPath x₀ (BasedPath.ofPath p))
  let cs : ChartedSpace H Mtilde :=
    lifted_covering_chartedSpace (H := H) π hcover
  letI : ChartedSpace H Mtilde := cs
  letI : IsManifold I ∞ Mtilde :=
    lifted_covering_chartedSpace_isManifold (I := I) (H := H) π hcover
  letI : SimplyConnectedSpace Mtilde :=
    TauCeti.UniversalCover.simplyConnectedSpace x₀
  have hsmooth : Manifold.IsSmoothCoveringMap I I π := by
    refine ⟨hcover, hsurj, ?_⟩
    intro p
    rcases lifted_projection_partial_diffeomorph
      (I := I) (H := H) π hcover p with ⟨Φ, hp, hΦ, -⟩
    exact ⟨Φ, hp, hΦ⟩
  have huniversal : Manifold.IsUniversalSmoothCoveringMap I I π :=
    ⟨hsmooth, inferInstance⟩
  refine ⟨Mtilde, inferInstance, inferInstance, inferInstance, π, huniversal, ?_⟩
  intro E' _ _ H' _ I' M' _ _ _ π' hπ'
  exact exists_diffeomorph_of_universal_smooth_covering_maps π huniversal π' hπ'

end

#print axioms exists_universal_smooth_covering_manifold
