import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import LeeSmoothLib.Ch03.Sec03_14.Proposition_3_9
import LeeSmoothLib.Ch02.Sec02_11.Definition_2_11_extra_2
import LeeSmoothLib.Ch05.Sec05_32.Definition_5_32_extra_2
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_2
import LeeSmoothLib.Ch05.Sec05_34.Lemma_5_34
import LeeSmoothLib.Ch08.Sec08_54.Lemma_8_6
import LeeSmoothLib.Ch08.Sec08_57.Definition_8_57_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Domain sampling for this item:
-- * source-facing vector fields on the submanifold `S` are expressed intrinsically as bundled
--   smooth sections `Cₛ^∞⟮J; E', TangentSpace J⟯`;
-- * ambient neighborhood and global extensions use the canonical bundled smooth-section owner on
--   the corresponding open submanifold of `M`;
-- * the restriction equalities are encoded by `VectorField.f_related` for the relevant subtype
--   inclusions, matching Lee's `X = Y|_S` wording without using the broken auxiliary
--   `VectorField.Along` layer.
-- Semantic recall note: `lean_leansearch` only surfaced generic section-extension lemmas, so the
-- source-facing global criterion is stated directly for intrinsic vector fields on `S`.

universe uE uE' uH uH' uM

noncomputable section

section

open Topology VectorField

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}
  [IsManifold I (∞ : ℕ∞ω) M]
  {S : Set M} [ChartedSpace H' S] [IsManifold J (∞ : ℕ∞ω) S]

local notation "SmoothAmbientVectorField" => Cₛ^∞⟮I; E, TangentSpace I⟯
local notation "SmoothSubmanifoldVectorField" =>
  Cₛ^∞⟮J; E', fun p : S ↦ TangentSpace J p⟯

private noncomputable abbrev immersionProjection {p : S}
    (hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p) :
    E →L[ℝ] E' :=
  (ContinuousLinearMap.fst ℝ E' hImm.complement).comp
    (hImm.equiv.symm).toContinuousLinearMap

/-- Push an intrinsic vector field on `S` into the ambient tangent bundle
along the subtype inclusion. -/
private def ambientSubtypePushforwardField
    (X : SmoothSubmanifoldVectorField) :
    ∀ p : S, TangentSpace I (p : M) :=
  fun p ↦ mfderiv J I (Subtype.val : S → M) p (X p)

/-- The ambient pushforward of a smooth intrinsic vector field is a
smooth section of the ambient tangent bundle along the embedded inclusion. -/
private lemma ambientSubtypePushforwardField_contMDiff
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) :
    ContMDiff J I.tangent (∞ : ℕ∞ω)
      (fun p : S ↦
        (⟨(p : M), ambientSubtypePushforwardField X p⟩ : TangentBundle I M)) := by
  -- View the pushed-forward field as the tangent map of the smooth inclusion applied to the
  -- smooth section `T% X`.
  have hInclContMDiff : ContMDiff J I (∞ : ℕ∞ω) (Subtype.val : S → M) :=
    hS.isImmersion.contMDiff
  have hTangent :
      ContMDiff J I.tangent (∞ : ℕ∞ω)
        (tangentMap J I (Subtype.val : S → M) ∘ (T% fun p : S ↦ X p)) := by
    exact
      (hInclContMDiff.contMDiff_tangentMap (by simp)).comp X.contMDiff
  simpa [ambientSubtypePushforwardField, Function.comp, tangentMap] using! hTangent

/-- Codomain-restricting the subtype inclusion to an ambient open
neighborhood of `S` preserves smoothness. -/
private lemma subtypeValToNeighborhood_contMDiff
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    {U : TopologicalSpace.Opens M} (hSU : (S : Set M) ⊆ U) :
    ContMDiff J I (∞ : ℕ∞ω) (fun p : S ↦ (⟨(p : M), hSU p.2⟩ : U)) := by
  -- Restrict the already smooth subtype inclusion to the chosen ambient open neighborhood.
  have hcomp :
      ContMDiff J I (∞ : ℕ∞ω)
        (Subtype.val ∘ fun p : S ↦ (⟨(p : M), hSU p.2⟩ : U)) := by
    simpa [Function.comp_def] using! hS.isImmersion.contMDiff
  exact
    (ContMDiff.subtypeVal_comp_iff U
      (fun p : S ↦ (⟨(p : M), hSU p.2⟩ : U))).mp hcomp

/-- Helper for Problem 8-15: ambient smoothness on `V ⊆ M` restricts along the open inclusion
`U ↪ M` to a smooth ambient tangent-bundle map on the open subtype. -/
private lemma ambientLocalFieldRestrictSmoothAmbientMap
    {U : TopologicalSpace.Opens M} {Xloc : ∀ y : M, TangentSpace I y} {V : Set M}
    (hXloc : ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% Xloc) V) :
    ContMDiffOn I I.tangent (∞ : ℕ∞ω) (fun y : U ↦ T% Xloc y.1) (Subtype.val ⁻¹' V) := by
  -- Compose the ambient tangent-bundle section with the open-subtype inclusion.
  exact
    hXloc.comp
      ((contMDiff_subtype_val : ContMDiff I I (∞ : ℕ∞ω) (Subtype.val : U → M)).contMDiffOn)
      (by
        intro y hy
        exact hy)

/-- Helper for Problem 8-15: pushing the pullback of an ambient vector field along an open
inclusion recovers the original ambient tangent-bundle section. -/
private lemma subtypeValMfderivInverseApply
    (U : TopologicalSpace.Opens M)
    (p : U) (w : TangentSpace I (p : M)) :
    mfderiv I I (Subtype.val : U → M) p
      ((mfderiv I I (Subtype.val : U → M) p).inverse w) = w := by
  -- The derivative of the open inclusion is invertible, so applying it cancels `.inverse`.
  simpa using
    (mfderiv_open_subset_inclusion_isInvertible U p).self_apply_inverse w

/-- Helper for Problem 8-15: pushing the pullback of an ambient vector field along an open
inclusion recovers the original ambient tangent-bundle section. -/
private lemma tangentMapSubtypeValPullbackEq
    (U : TopologicalSpace.Opens M)
    (X : ∀ p : M, TangentSpace I p)
    (p : U) :
    tangentMap I I (Subtype.val : U → M)
      (T% (VectorField.mpullback I I (Subtype.val : U → M) X) p) =
      T% X p.1 := by
  -- Expand the pullback formula once and cancel the derivative of the open inclusion.
  simpa [tangentMap, VectorField.mpullback_apply, Bundle.TotalSpace.mk_inj] using
    subtypeValMfderivInverseApply U p (X p.1)

/-- Helper for Problem 8-15: restricting an ambient smooth local vector field to an ambient open
subtype yields a smooth local vector field on that open subtype. -/
private lemma ambientLocalFieldRestrictSmoothOnOpenSubtype
    {U : TopologicalSpace.Opens M} {Xloc : ∀ y : M, TangentSpace I y} {V : Set M}
    (hXloc : ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% Xloc) V) :
    let g : ∀ y : U, TangentSpace I y :=
      VectorField.mpullback I I (Subtype.val : U → M) Xloc
    ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% g) (Subtype.val ⁻¹' V) := by
  let g : ∀ y : U, TangentSpace I y :=
    VectorField.mpullback I I (Subtype.val : U → M) Xloc
  -- Route correction: keep the field in pullback normal form on the open subtype and postpone the
  -- ambient identification to the final `f_related` packaging step.
  simpa [g] using
    hXloc.mpullback_vectorField_preimage
      (contMDiff_subtype_val : ContMDiff I I (∞ : ℕ∞ω) (Subtype.val : U → M))
      (by
        intro p hp
        simpa using mfderiv_open_subset_inclusion_isInvertible U p)
      (by simp)

/-- Pointwise smooth ambient extensions of the prescribed ambient tangent
vectors along `S` glue to a smooth vector field on an open neighborhood of `S`. -/
private lemma exists_local_vectorField_extension_of_pointwiseLocalAmbientExtension
    [T2Space M] [SigmaCompactSpace M]
    (X : ∀ p : S, TangentSpace I (p : M))
    (hX : ∀ p : S, ContMDiffVectorFieldLocalExtension X p) :
    ∃ U : TopologicalSpace.Opens M, ∃ hSU : (S : Set M) ⊆ U,
      ∃ Y : Cₛ^∞⟮I; E, fun p : U ↦ TangentSpace I p⟯,
        ∀ p : S,
          Y ⟨(p : M), hSU p.2⟩ =
            (mfderiv I I (Subtype.val : U → M) ⟨(p : M), hSU p.2⟩).inverse (X p) := by
  classical
  letI : SecondCountableTopology H := I.secondCountableTopology
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let Uset : Set M := ⋃ p : S, (hX p).V
  let U : TopologicalSpace.Opens M := ⟨Uset, isOpen_iUnion fun p ↦ (hX p).isOpen_V⟩
  letI : SecondCountableTopology U := inferInstance
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  letI : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  letI : IsManifold I (∞ : ℕ∞ω) U := inferInstance
  have hSU : (S : Set M) ⊆ U := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, (hX ⟨x, hx⟩).mem_V⟩
  let t : ∀ x : U, Set (TangentSpace I x) := fun x ↦
    if hx : ((x : U) : M) ∈ S then
      {(mfderiv I I (Subtype.val : U → M) x).inverse (X ⟨((x : U) : M), hx⟩)}
    else Set.univ
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    by_cases hx : ((x : U) : M) ∈ S
    · have hxConv :
          Convex ℝ
            ({(mfderiv I I (Subtype.val : U → M) x).inverse (X ⟨((x : U) : M), hx⟩)} :
              Set (TangentSpace I x)) :=
        convex_singleton ((mfderiv I I (Subtype.val : U → M) x).inverse (X ⟨((x : U) : M), hx⟩))
      simpa [t, hx] using hxConv
    · simpa [t, hx] using (convex_univ : Convex ℝ (Set.univ : Set (TangentSpace I x)))
  have hloc :
      ∀ x : U, ∃ W ∈ nhds x, ∃ g : ∀ y : U, TangentSpace I y,
        ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% g) W ∧
          ∀ y ∈ W, g y ∈ t y := by
    intro x
    rcases Set.mem_iUnion.1 x.2 with ⟨p, hxVp⟩
    let data := hX p
    let W : Set U := Subtype.val ⁻¹' data.V
    let g : ∀ y : U, TangentSpace I y :=
      VectorField.mpullback I I (Subtype.val : U → M) data.Xloc
    refine ⟨W, ?_, g, ?_, ?_⟩
    · -- Use the ambient extension neighborhood of the chosen covering point as a neighborhood
      -- inside the open subtype `U`.
      exact (data.isOpen_V.preimage continuous_subtype_val).mem_nhds hxVp
    · -- Restrict the ambient local field to the open subtype by reinterpreting the same section
      -- inclusion `U ↪ M`.
      simpa [g] using
        ambientLocalFieldRestrictSmoothOnOpenSubtype data.contMDiffOn
    · intro y hyW
      by_cases hyS : ((y : U) : M) ∈ S
      · have hyEqLoc : data.Xloc y = X ⟨(y : M), hyS⟩ :=
          data.eq_source ⟨(y : M), hyS⟩ hyW
        -- On the source patch, the pulled-back local field is the inverse transport of the
        -- prescribed ambient vector through the open inclusion derivative.
        simpa [g, t, hyS, VectorField.mpullback_apply, hyEqLoc]
      · simp [g, t, hyS]
  -- Globalize the compatible local ambient extensions over the open neighborhood they cover.
  obtain ⟨Y, hY⟩ :
      ∃ Y : Cₛ^∞⟮I; E, fun p : U ↦ TangentSpace I p⟯, ∀ x : U, Y x ∈ t x := by
    simpa [t] using
      exists_contMDiffSection_forall_mem_convex_of_local I (TangentSpace I) t ht hloc
  refine ⟨U, hSU, Y, ?_⟩
  intro p
  have hpS : ((⟨(p : M), hSU p.2⟩ : U) : M) ∈ S := p.2
  simpa [t, hpS] using hY ⟨(p : M), hSU p.2⟩

/-- Once the pointwise local ambient extension problem is solved, the
closed-subset extension lemma upgrades proper embeddedness to a global extension theorem. -/
private lemma properlyEmbedded_vectorField_globalExtension_of_pointwiseLocalAmbientExtension
    [T2Space M] [SigmaCompactSpace M]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (hProper : S.IsProperlyEmbedded)
    (X : SmoothSubmanifoldVectorField)
    (hX :
      ∀ p : S,
        ContMDiffVectorFieldLocalExtension
          (ambientSubtypePushforwardField X : ∀ p : S, TangentSpace I (p : M)) p) :
    ∃ Z : SmoothAmbientVectorField,
      VectorField.f_related (Subtype.val : S → M) X Z := by
  have hClosed : IsClosed S := hProper.isClosed
  obtain ⟨Z, hZ⟩ :=
    exists_supported_contMDiff_vectorField_extension_of_isClosed
      hClosed isOpen_univ
      (by
        intro x hx
        simp)
      (ambientSubtypePushforwardField X) hX
  refine ⟨⟨Z, hZ.contMDiff⟩, ?_⟩
  refine ⟨hS.isImmersion.contMDiff, ?_⟩
  intro p
  -- The closed-subset extension agrees with the ambient pushforward field along `S`.
  simpa [ambientSubtypePushforwardField] using (hZ.eq_source p).symm

/-- Helper for Problem 8-15: a smooth Euclidean coordinate map on a set contained in one
tangent-bundle trivialization base reconstructs a smooth ambient local vector field. -/
private lemma ambientFieldFromTrivializationCoordinates_contMDiffOn
    (p : M) {V : Set M} (hV_open : IsOpen V) {χ : M → E}
    (hχ : ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V)
    (hV_base : V ⊆ (trivializationAt E (TangentSpace I) p).baseSet) :
    let Xloc : ∀ y : M, TangentSpace I y :=
      fun y ↦ (trivializationAt E (TangentSpace I) p).symm y (χ y)
    ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% Xloc) V := by
  let τ := trivializationAt E (TangentSpace I) p
  let Xloc : ∀ y : M, TangentSpace I y := fun y ↦ τ.symm y (χ y)
  have hcoord :
      ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω)
        (fun y ↦ (τ ⟨y, Xloc y⟩).2) V := by
    -- The chosen trivialization reads the rebuilt field back as the original coordinate map `χ`.
    refine hχ.congr ?_
    intro y hy
    simpa [τ, Xloc] using congrArg Prod.snd (τ.apply_mk_symm (hV_base hy) (χ y))
  -- Convert smoothness of the trivialized coordinate back to smoothness of the tangent-bundle
  -- section on the same ambient patch.
  exact
    (Bundle.Trivialization.contMDiffOn_section_iff τ hV_open hV_base).2 hcoord

/-- Helper for Problem 8-15: if tangent-bundle trivialization coordinates match a prescribed
ambient tangent section along `S`, then the rebuilt ambient field agrees with that section on `S`.
-/
private lemma ambientFieldFromTrivializationCoordinates_eq_source
    (p : M) {V : Set M} {χ : M → E}
    {X : ∀ q : S, TangentSpace I (q : M)}
    (hV_base : V ⊆ (trivializationAt E (TangentSpace I) p).baseSet)
    (hχ :
      ∀ q : S, (q : M) ∈ V →
        χ q = (trivializationAt E (TangentSpace I) p ⟨(q : M), X q⟩).2) :
    let Xloc : ∀ y : M, TangentSpace I y :=
      fun y ↦ (trivializationAt E (TangentSpace I) p).symm y (χ y)
    ∀ q : S, (q : M) ∈ V → Xloc q = X q := by
  let τ := trivializationAt E (TangentSpace I) p
  let Xloc : ∀ y : M, TangentSpace I y := fun y ↦ τ.symm y (χ y)
  dsimp only
  intro q hqV
  have hqBase : (q : M) ∈ τ.baseSet := hV_base hqV
  have hpair :
      Bundle.TotalSpace.mk' E (q : M) (Xloc q) =
        Bundle.TotalSpace.mk' E (q : M) (X q) := by
    -- Rewrite both fields through the same trivialization coordinates and then cancel `τ.symm`.
    calc
      Bundle.TotalSpace.mk' E (q : M) (Xloc q)
          = τ.toOpenPartialHomeomorph.symm ((q : M), χ q) := by
              simpa [Xloc] using τ.mk_symm hqBase (χ q)
      _ = τ.toOpenPartialHomeomorph.symm ((q : M), (τ ⟨(q : M), X q⟩).2) := by
              rw [hχ q hqV]
      _ = Bundle.TotalSpace.mk' E (q : M) (τ.symm (q : M) (τ ⟨(q : M), X q⟩).2) := by
              simpa using (τ.mk_symm hqBase ((τ ⟨(q : M), X q⟩).2)).symm
      _ = Bundle.TotalSpace.mk' E (q : M) (X q) := by
              congr
              exact τ.symm_apply_apply_mk hqBase (X q)
  simpa [τ, Xloc] using congrArg Bundle.TotalSpace.snd hpair

/-- Helper for Problem 8-15: on the pullback of the ambient tangent-bundle trivialization base set
to `S`, the pushed-forward intrinsic field has smooth ambient trivialization coordinates. -/
private lemma ambientPushforwardTrivializationCoordinates_contMDiffOn
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) (p : S) :
    let τ := trivializationAt E (TangentSpace I) (p : M)
    let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
    ContMDiffOn J 𝓘(ℝ, E) (∞ : ℕ∞ω)
      (fun q : S ↦ (τ ⟨(q : M), ambientSubtypePushforwardField X q⟩).2) U := by
  let τ := trivializationAt E (TangentSpace I) (p : M)
  let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
  let fS : S → TangentBundle I M :=
    fun q ↦ ⟨(q : M), ambientSubtypePushforwardField X q⟩
  have hSection :
      ContMDiffOn J I.tangent (∞ : ℕ∞ω) fS U := by
    -- Restrict the globally smooth ambient pushed-forward field to the trivialization base set.
    simpa [fS] using
      (ambientSubtypePushforwardField_contMDiff hS X).contMDiffOn
  have hMaps : Set.MapsTo fS U τ.source := by
    intro q hq
    -- The trivialization source is exactly the pullback of its base set to the total space.
    simpa [fS, U, τ] using hq
  -- Read the smooth tangent-bundle section in the chosen ambient trivialization coordinates.
  exact ((τ.contMDiffOn_iff hMaps).mp hSection).2

/-- Helper for Problem 8-15: once a smooth local section `σ : M → S` fixes the embedded
submanifold near `p` and lands in the source-side trivialization domain, composing the source
coordinate map with `σ` yields the required ambient coordinate extension. -/
private lemma ambientCoordinateExtensionOfLocalSection
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) (p : S)
    {V : Set M}
    {σ : M → S}
    (hσ : ContMDiffOn I J (∞ : ℕ∞ω) σ V)
    (hσ_mem :
      ∀ x ∈ V, ((σ x : S) : M) ∈ (trivializationAt E (TangentSpace I) (p : M)).baseSet)
    (hσ_eq : ∀ q : S, (q : M) ∈ V → σ q = q) :
    ∃ χ : M → E,
      ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V ∧
        ∀ q : S, (q : M) ∈ V →
          χ q =
            (trivializationAt E (TangentSpace I) (p : M)
              ⟨(q : M), ambientSubtypePushforwardField X q⟩).2 := by
  let τ := trivializationAt E (TangentSpace I) (p : M)
  let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
  let ψ : S → E := fun q ↦ (τ ⟨(q : M), ambientSubtypePushforwardField X q⟩).2
  have hψ :
      ContMDiffOn J 𝓘(ℝ, E) (∞ : ℕ∞ω) ψ U := by
    -- The intrinsic pushed-forward field is already smooth in these source-side coordinates.
    simpa [τ, U, ψ] using ambientPushforwardTrivializationCoordinates_contMDiffOn hS X p
  have hσ_maps : Set.MapsTo σ V U := by
    -- The local section is assumed to stay inside the trivialization domain used for `ψ`.
    intro x hx
    simpa [τ, U] using! hσ_mem x hx
  refine ⟨ψ ∘ σ, ?_, ?_⟩
  · -- Compose the smooth source coordinate map with the smooth local section.
    simpa [Function.comp, ψ] using hψ.comp hσ hσ_maps
  · intro q hqV
    -- On points of `S`, the local section is the identity, so the composed coordinates agree with
    -- the original pushed-forward field coordinates.
    rw [Function.comp, hσ_eq q hqV]

/-- Helper for Problem 8-15: if the projected immersion coordinates stay in the source chart
target on `V`, the standard projected chart formula defines a smooth `S`-valued local section
there. -/
private lemma immersionProjectedLocalSection_contMDiffOn
    {p : S}
    (hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p)
    {V : Set M}
    (hV_cod : V ⊆ hImm.codChart.source)
    (hV_target :
      let π : E →L[ℝ] E' := immersionProjection hImm
      ∀ x ∈ V, π ((hImm.codChart.extend I) x) ∈ (hImm.domChart.extend J).target) :
    let π : E →L[ℝ] E' := immersionProjection hImm
    let σ : M → S := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
    ContMDiffOn I J (∞ : ℕ∞ω) σ V := by
  let π : E →L[ℝ] E' := immersionProjection hImm
  let σ : M → S := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
  have hdomChart_mem :
      hImm.domChart ∈ IsManifold.maximalAtlas J (∞ : ℕ∞ω) S :=
    IsManifold.maximalAtlas_subset_of_le
      (show (∞ : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp) hImm.domChart_mem_maximalAtlas
  have hdomChartSymm :
      ContMDiffOn 𝓘(ℝ, E') J (∞ : ℕ∞ω) (hImm.domChart.extend J).symm
        (hImm.domChart.extend J).target := by
    -- Rewrite the source chart inverse on its natural extended target.
    convert contMDiffOn_extend_symm hdomChart_mem using 2
    simpa [Set.inter_comm] using (J.image_eq hImm.domChart.target).symm
  have hcodChart_mem :
      hImm.codChart ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M :=
    IsManifold.maximalAtlas_subset_of_le
      (show (∞ : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp) hImm.codChart_mem_maximalAtlas
  have hcodExt :
      ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) (hImm.codChart.extend I) V := by
    -- Restrict the ambient codomain chart extension to the chosen ambient patch.
    exact (hImm.codChart.contMDiffOn_extend hcodChart_mem).mono hV_cod
  have hproj :
      ContMDiffOn I 𝓘(ℝ, E') (∞ : ℕ∞ω) (π ∘ (hImm.codChart.extend I)) V := by
    -- Postcompose the ambient chart coordinates with the fixed immersion projection.
    simpa [Function.comp] using π.contDiff.contMDiff.comp_contMDiffOn hcodExt
  have hmaps :
      Set.MapsTo (π ∘ (hImm.codChart.extend I)) V (hImm.domChart.extend J).target := by
    intro x hx
    simpa [π, Function.comp] using hV_target x hx
  -- Compose the smooth projected ambient coordinates with the smooth inverse source chart.
  simpa [σ, π, Function.comp] using! hdomChartSymm.comp hproj hmaps

/-- Helper for Problem 8-15: on source points whose ambient image lies in the chosen patch, the
projected chart local section is the identity. -/
private lemma immersionProjectedLocalSection_eqSelf
    {p q : S}
    (hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E →L[ℝ] E' := immersionProjection hImm
    let σ : M → S := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
    σ q = q := by
  let π : E →L[ℝ] E' := immersionProjection hImm
  let σ : M → S := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
  have hq_proj :
      π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q :=
    immersionProjectionEqDomainCoordinates hImm hq
  -- Normalize the projected immersion coordinates back to the intrinsic source chart coordinate.
  calc
    σ q = (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) q)) := rfl
    _ = (hImm.domChart.extend J).symm ((hImm.domChart.extend J) q) := by rw [hq_proj]
    _ = q := by
      exact hImm.domChart.extend_left_inv hq

/-- The differential of an embedded inclusion is injective.  We prove the fact needed below
directly from the immersion normal form, rather than importing the chapter-level rank criterion:
the projected ambient chart gives a smooth local left inverse to the inclusion.

The interior-point hypothesis is used only to produce an ambient-open neighborhood on which that
left inverse is defined.  Immersion already implies injectivity of `mfderiv` at boundary points
as well, but packaging a local left inverse through chart interiors uses
`BoundarylessManifold`. -/
private lemma isSmoothEmbedding_mfderiv_injective
    [BoundarylessManifold J S]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (p : S) :
    Function.Injective (mfderiv J I (Subtype.val : S → M) p) := by
  let hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p :=
    hS.isImmersion.isImmersionAt p
  let π : E →L[ℝ] E' := immersionProjection hImm
  let σ : M → S := fun x ↦
    (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
  let Ω : Set E' := interior (hImm.domChart.extend J).target
  let V : Set M :=
    hImm.codChart.source ∩ (hImm.codChart.extend I) ⁻¹' (π ⁻¹' Ω)
  have hΩ_open : IsOpen Ω := isOpen_interior
  have hV_open : IsOpen V := by
    simpa [V] using hImm.codChart.isOpen_extend_preimage (hΩ_open.preimage π.continuous)
  have hpΩ : (hImm.domChart.extend J) p ∈ Ω := by
    exact
      (J.isInteriorPoint_iff_of_mem_maximalAtlas
        (n := (∞ : ℕ∞ω)) (by simp) hImm.domChart_mem_maximalAtlas
        hImm.mem_domChart_source).1 BoundarylessManifold.isInteriorPoint
  have hp_proj : π ((hImm.codChart.extend I) p) = (hImm.domChart.extend J) p := by
    simpa [π] using immersionProjectionEqDomainCoordinates hImm hImm.mem_domChart_source
  have hpV : (p : M) ∈ V := by
    refine ⟨hImm.mem_codChart_source, ?_⟩
    change π ((hImm.codChart.extend I) (p : M)) ∈ Ω
    rw [hp_proj]
    exact hpΩ
  have hV_cod : V ⊆ hImm.codChart.source := fun _ hx ↦ hx.1
  have hV_target : ∀ x ∈ V, π ((hImm.codChart.extend I) x) ∈
      (hImm.domChart.extend J).target := by
    intro x hx
    exact interior_subset hx.2
  have hσOn : ContMDiffOn I J (∞ : ℕ∞ω) σ V := by
    simpa only [hImm, π, σ] using
      immersionProjectedLocalSection_contMDiffOn hImm hV_cod hV_target
  have hσAt : MDifferentiableAt I J σ (p : M) :=
    (hσOn (p : M) hpV).contMDiffAt (hV_open.mem_nhds hpV) |>.mdifferentiableAt (by simp)
  have hInclAt : MDifferentiableAt J I (Subtype.val : S → M) p :=
    hS.isImmersion.contMDiff.mdifferentiableAt (by simp)
  have hEq : (σ ∘ (Subtype.val : S → M)) =ᶠ[𝓝 p] id := by
    apply Set.EqOn.eventuallyEq_of_mem _
      (hImm.domChart.open_source.mem_nhds hImm.mem_domChart_source)
    intro q hq
    exact immersionProjectedLocalSection_eqSelf hImm hq
  have hσp : σ (p : M) = p := by
    exact immersionProjectedLocalSection_eqSelf hImm hImm.mem_domChart_source
  intro v w hvw
  have hcomp := mfderiv_comp_apply p hσAt hInclAt (v - w)
  rw [hσp] at hcomp
  have hzero : mfderiv J I (Subtype.val : S → M) p (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hid : mfderiv J J id p (v - w) = v - w := by
    rw [mfderiv_id]
    rfl
  have hcompEq :
      mfderiv J J (σ ∘ (Subtype.val : S → M)) p = mfderiv J J id p :=
    hEq.mfderiv_eq
  unfold TangentSpace at hcompEq
  have hcompZero :
      mfderiv J J (σ ∘ (Subtype.val : S → M)) p (v - w) = 0 := by
    calc
      _ = mfderiv I J σ (p : M)
          (mfderiv J I (Subtype.val : S → M) p (v - w)) := hcomp
      _ = 0 := by rw [hzero, map_zero]
  have : v - w = 0 := by
    calc
      v - w = mfderiv J J id p (v - w) := hid.symm
      _ = mfderiv J J (σ ∘ (Subtype.val : S → M)) p (v - w) := by
        rw [hcompEq]
        rfl
      _ = 0 := hcompZero
  exact sub_eq_zero.mp this

/-- Helper for Problem 8-15: after rewriting the pushed-forward field in one ambient tangent
trivialization, the resulting source-chart coordinate representative is smooth on the part of the
source chart target where that trivialization is defined. -/
private lemma sourceCoordinateRepresentative_contMDiffOn
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) (p : S) :
    let τ := trivializationAt E (TangentSpace I) (p : M)
    let hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p :=
      hS.isImmersion.isImmersionAt p
    let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
    let ψcoord : E' → E := fun z ↦
      (τ
        ⟨(((hImm.domChart.extend J).symm z : S) : M),
          ambientSubtypePushforwardField X ((hImm.domChart.extend J).symm z)⟩).2
    let T : Set E' := (hImm.domChart.extend J).target ∩ ((hImm.domChart.extend J).symm ⁻¹' U)
    ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) (∞ : ℕ∞ω) ψcoord T := by
  let τ := trivializationAt E (TangentSpace I) (p : M)
  let hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p :=
    hS.isImmersion.isImmersionAt p
  let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
  let ψ : S → E := fun q ↦ (τ ⟨(q : M), ambientSubtypePushforwardField X q⟩).2
  let ψcoord : E' → E := fun z ↦
    (τ
      ⟨(((hImm.domChart.extend J).symm z : S) : M),
        ambientSubtypePushforwardField X ((hImm.domChart.extend J).symm z)⟩).2
  let T : Set E' := (hImm.domChart.extend J).target ∩ ((hImm.domChart.extend J).symm ⁻¹' U)
  have hψ :
      ContMDiffOn J 𝓘(ℝ, E) (∞ : ℕ∞ω) ψ U := by
    -- The pushed-forward field already has smooth ambient trivialization coordinates on the source
    -- patch where the tangent-bundle trivialization is defined.
    simpa [τ, U, ψ] using ambientPushforwardTrivializationCoordinates_contMDiffOn hS X p
  have hdomChart_mem :
      hImm.domChart ∈ IsManifold.maximalAtlas J (∞ : ℕ∞ω) S :=
    IsManifold.maximalAtlas_subset_of_le
      (show (∞ : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp) hImm.domChart_mem_maximalAtlas
  have hdomChartSymm :
      ContMDiffOn 𝓘(ℝ, E') J (∞ : ℕ∞ω) (hImm.domChart.extend J).symm
        (hImm.domChart.extend J).target := by
    -- Rewrite the inverse source chart onto its natural extended target once and compose there.
    convert contMDiffOn_extend_symm hdomChart_mem using 2
    simpa [Set.inter_comm] using (J.image_eq hImm.domChart.target).symm
  have hdomChartSymmT :
      ContMDiffOn 𝓘(ℝ, E') J (∞ : ℕ∞ω) (hImm.domChart.extend J).symm T := by
    exact hdomChartSymm.mono fun _ hz ↦ hz.1
  have hmaps : T ⊆ (hImm.domChart.extend J).symm ⁻¹' U := by
    intro z hz
    exact hz.2
  -- Pull the source-side coordinate map back along the smooth inverse source chart.
  change
    ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) (∞ : ℕ∞ω)
      (ψ ∘ (hImm.domChart.extend J).symm) T
  exact hψ.comp hdomChartSymmT hmaps

/-- Helper for Problem 8-15: the source-chart coordinate representative is `Function.IsSmoothOn`
when `S` is boundaryless, so the chart target (and therefore `T`) is open in `E'`.

If `S` has boundary, `T` is only relatively open in `range J`, which is typically a half-space.
An ambient-open Euclidean extension of `ψcoord` off that half-space is a Seeley-extension
statement and is not proved here. -/
private lemma sourceCoordinateRepresentative_isSmoothOn
    [BoundarylessManifold J S]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) (p : S) :
    let τ := trivializationAt E (TangentSpace I) (p : M)
    let hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p :=
      hS.isImmersion.isImmersionAt p
    let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
    let ψcoord : E' → E := fun z ↦
      (τ
        ⟨(((hImm.domChart.extend J).symm z : S) : M),
          ambientSubtypePushforwardField X ((hImm.domChart.extend J).symm z)⟩).2
    let T : Set E' := (hImm.domChart.extend J).target ∩ ((hImm.domChart.extend J).symm ⁻¹' U)
    (fun z : T ↦ ψcoord z).IsSmoothOn (𝓘(ℝ, E')) 𝓘(ℝ, E) := by
  let τ := trivializationAt E (TangentSpace I) (p : M)
  let hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p :=
    hS.isImmersion.isImmersionAt p
  let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
  let ψcoord : E' → E := fun z ↦
    (τ
      ⟨(((hImm.domChart.extend J).symm z : S) : M),
        ambientSubtypePushforwardField X ((hImm.domChart.extend J).symm z)⟩).2
  let T : Set E' := (hImm.domChart.extend J).target ∩ ((hImm.domChart.extend J).symm ⁻¹' U)
  have hdomTargetOpen : IsOpen (hImm.domChart.extend J).target := by
    rw [← subset_interior_iff_isOpen]
    intro z hz
    let q : S := (hImm.domChart.extend J).symm z
    have hqSource : q ∈ hImm.domChart.source := by
      simpa [q, hImm.domChart.extend_source] using
        (hImm.domChart.extend J).map_target hz
    have hqInterior :
        (hImm.domChart.extend J) q ∈ interior (hImm.domChart.extend J).target := by
      exact
        (J.isInteriorPoint_iff_of_mem_maximalAtlas
          (n := (∞ : ℕ∞ω)) (by simp) hImm.domChart_mem_maximalAtlas hqSource).1
          BoundarylessManifold.isInteriorPoint
    have hzEq : (hImm.domChart.extend J) q = z := by
      exact (hImm.domChart.extend J).right_inv hz
    rw [hzEq] at hqInterior
    exact hqInterior
  have hUOpen : IsOpen U := by
    exact τ.open_baseSet.preimage continuous_subtype_val
  have hTOpen : IsOpen T := by
    exact
      hImm.domChart.continuousOn_extend_symm.isOpen_inter_preimage
        hdomTargetOpen hUOpen
  have hψcoord :
      ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) (∞ : ℕ∞ω) ψcoord T := by
    simpa only [τ, hImm, U, ψcoord, T] using!
      sourceCoordinateRepresentative_contMDiffOn hS X p
  rw [Function.isSmoothOn_iff_exists_local_extension]
  intro z
  refine ⟨T, hTOpen, z.2, ψcoord, hψcoord, ?_⟩
  intro w hw
  rfl

/-- Helper for Problem 8-15: in one ambient tangent-bundle trivialization around `p`, the
pushed-forward intrinsic field has a smooth ambient coordinate extension.

The `BoundarylessManifold` hypothesis is used to obtain an open Euclidean neighborhood of the
source-chart representative.  A source-with-boundary variant would replace that step by a
Seeley extension off `range J` and is not claimed here. -/
private lemma embeddedPointwiseLocalAmbientCoordinateExtension
    [BoundarylessManifold J S]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) (p : S) :
    ∃ V : Set M,
      IsOpen V ∧
        (p : M) ∈ V ∧
          V ⊆ (trivializationAt E (TangentSpace I) (p : M)).baseSet ∧
            ∃ χ : M → E,
              ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V ∧
                ∀ q : S, (q : M) ∈ V →
                  χ q =
                    (trivializationAt E (TangentSpace I) (p : M)
                      ⟨(q : M), ambientSubtypePushforwardField X q⟩).2 := by
  let τ := trivializationAt E (TangentSpace I) (p : M)
  let hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p :=
    hS.isImmersion.isImmersionAt p
  let π : E →L[ℝ] E' := immersionProjection hImm
  let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
  let ψ : S → E := fun q ↦ (τ ⟨(q : M), ambientSubtypePushforwardField X q⟩).2
  let ψcoord : E' → E := ψ ∘ (hImm.domChart.extend J).symm
  let T : Set E' := (hImm.domChart.extend J).target ∩ ((hImm.domChart.extend J).symm ⁻¹' U)
  let z0 : E' := (hImm.domChart.extend J) p
  have hpτ : (p : M) ∈ τ.baseSet := FiberBundle.mem_baseSet_trivializationAt' (p : M)
  have hpSource : p ∈ (hImm.domChart.extend J).source := by
    simpa [hImm.domChart.extend_source] using hImm.mem_domChart_source
  have hpT : z0 ∈ T := by
    refine ⟨(hImm.domChart.extend J).map_source hpSource, ?_⟩
    change (hImm.domChart.extend J).symm ((hImm.domChart.extend J) p) ∈ U
    rw [hImm.domChart.extend_left_inv hImm.mem_domChart_source]
    exact hpτ
  have hψcoord :
      ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) (∞ : ℕ∞ω) ψcoord T := by
    -- The chart-side representative is already smooth on the source chart target; only the
    -- off-target Euclidean extension step remains.
    simpa only [τ, hImm, U, ψ, ψcoord, T, Function.comp] using!
      sourceCoordinateRepresentative_contMDiffOn hS X p
  have hψcoordSmoothOn :
      (fun z : T ↦ ψcoord z).IsSmoothOn (𝓘(ℝ, E')) 𝓘(ℝ, E) := by
    -- Route correction: use the source-facing local-extension owner on `T`, then extract the
    -- ambient-open Euclidean extension data needed below.
    simpa only [τ, hImm, U, ψcoord, T] using!
      sourceCoordinateRepresentative_isSmoothOn hS X p
  have hExtend :
      ∃ Ω : Set E', IsOpen Ω ∧ z0 ∈ Ω ∧
        ∃ ψext : E' → E,
          ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) (∞ : ℕ∞ω) ψext Ω ∧
            ∀ z, z ∈ Ω → z ∈ T → ψext z = ψcoord z := by
    rw [Function.isSmoothOn_iff_exists_local_extension] at hψcoordSmoothOn
    rcases hψcoordSmoothOn ⟨z0, hpT⟩ with ⟨Ω, hΩ_open, hz0Ω, ψext, hψext, hψext_eq⟩
    refine ⟨Ω, hΩ_open, hz0Ω, ψext, hψext, ?_⟩
    intro z hzΩ hzT
    exact hψext_eq ⟨z, hzT⟩ hzΩ
  rcases hExtend with ⟨Ω, hΩ_open, hz0Ω, ψext, hψext, hψext_eq⟩
  have hSubtypeVal : IsInducing (Subtype.val : S → M) := IsInducing.subtypeVal
  have hOpenSource :
      ∃ W : Set M, IsOpen W ∧ Subtype.val ⁻¹' W = hImm.domChart.source := by
    exact hSubtypeVal.isOpen_iff.mp hImm.domChart.open_source
  rcases hOpenSource with ⟨W, hW_open, hW_eq⟩
  let V : Set M :=
    τ.baseSet ∩ (W ∩ (hImm.codChart.source ∩ (hImm.codChart.extend I) ⁻¹' (π ⁻¹' Ω)))
  let χ : M → E := fun x ↦ ψext (π ((hImm.codChart.extend I) x))
  have hπΩ_open : IsOpen (π ⁻¹' Ω) := hΩ_open.preimage π.continuous
  have hcodPatch_open :
      IsOpen (hImm.codChart.source ∩ (hImm.codChart.extend I) ⁻¹' (π ⁻¹' Ω)) := by
    simpa using hImm.codChart.isOpen_extend_preimage hπΩ_open
  have hV_open : IsOpen V := by
    simpa [V] using τ.open_baseSet.inter (hW_open.inter hcodPatch_open)
  have hpW : (p : M) ∈ W := by
    have hpPre : p ∈ Subtype.val ⁻¹' W := by
      rw [hW_eq]
      exact hImm.mem_domChart_source
    exact hpPre
  have hp_proj : π ((hImm.codChart.extend I) p) = z0 := by
    dsimp [z0]
    simpa [π] using immersionProjectionEqDomainCoordinates hImm hImm.mem_domChart_source
  have hpV : (p : M) ∈ V := by
    refine ⟨hpτ, hpW, hImm.mem_codChart_source, ?_⟩
    simpa [Function.comp] using hp_proj.symm ▸ hz0Ω
  have hV_base : V ⊆ τ.baseSet := by
    intro x hx
    exact hx.1
  have hV_cod : V ⊆ hImm.codChart.source := by
    intro x hx
    exact hx.2.2.1
  have hχ :
      ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V := by
    have hcodChart_mem :
        hImm.codChart ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M :=
      IsManifold.maximalAtlas_subset_of_le
        (show (∞ : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp) hImm.codChart_mem_maximalAtlas
    have hcodExt :
        ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) (hImm.codChart.extend I) V := by
      -- Restrict the ambient codomain chart extension to the final ambient patch.
      exact (hImm.codChart.contMDiffOn_extend hcodChart_mem).mono hV_cod
    have hproj :
        ContMDiffOn I 𝓘(ℝ, E') (∞ : ℕ∞ω) (π ∘ (hImm.codChart.extend I)) V := by
      -- Postcompose the ambient chart coordinates with the fixed immersion projection.
      simpa [Function.comp] using π.contDiff.contMDiff.comp_contMDiffOn hcodExt
    have hmaps : Set.MapsTo (π ∘ (hImm.codChart.extend I)) V Ω := by
      intro x hx
      exact hx.2.2.2
    -- Compose the ambient codomain chart with the Euclidean extension built near `z0`.
    simpa [χ, Function.comp] using! hψext.comp hproj hmaps
  refine ⟨V, hV_open, hpV, hV_base, χ, hχ, ?_⟩
  intro q hqV
  have hqτ : (q : M) ∈ τ.baseSet := hqV.1
  have hqW : (q : M) ∈ W := hqV.2.1
  have hqΩ : π ((hImm.codChart.extend I) q) ∈ Ω := hqV.2.2.2
  have hqDom : q ∈ hImm.domChart.source := by
    have hqPre : q ∈ Subtype.val ⁻¹' W := hqW
    rw [hW_eq] at hqPre
    exact hqPre
  have hq_proj : π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q := by
    simpa [π] using immersionProjectionEqDomainCoordinates hImm hqDom
  have hqSource : q ∈ (hImm.domChart.extend J).source := by
    simpa [hImm.domChart.extend_source] using hqDom
  have hqT : π ((hImm.codChart.extend I) q) ∈ T := by
    refine ⟨?_, ?_⟩
    · rw [hq_proj]
      exact (hImm.domChart.extend J).map_source hqSource
    · change (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) q)) ∈ U
      rw [hq_proj]
      rw [hImm.domChart.extend_left_inv hqDom]
      exact hqτ
  -- On source points, the ambient codomain chart projects back to the intrinsic source chart, so
  -- the Euclidean extension agrees with the original tangent-trivialization coordinates.
  calc
    χ q = ψcoord (π ((hImm.codChart.extend I) q)) := hψext_eq _ hqΩ hqT
    _ = ψcoord ((hImm.domChart.extend J) q) := by rw [hq_proj]
    _ = ψ q := by
      unfold ψcoord
      simp only [Function.comp_apply]
      rw [hImm.domChart.extend_left_inv hqDom]
    _ =
        (trivializationAt E (TangentSpace I) (p : M)
          ⟨(q : M), ambientSubtypePushforwardField X q⟩).2 := rfl

/-- Problem 8-15 (1). EXTENSION LEMMA FOR VECTOR FIELDS ON SUBMANIFOLDS: Suppose `M` is a smooth
manifold and `S ⊆ M` is a boundaryless embedded smooth submanifold. Given
`X ∈ 𝓧(S)`, there is a smooth vector field `Y` on a neighborhood of `S` in `M` such that
`X = Y|_S`. In Lean, the restriction equality is encoded by `VectorField.f_related` for the
inclusion `S ↪ U` into the chosen open neighborhood `U`.

The source-boundaryless restriction is used because the chart-target set `T ⊆ E'` must be open
in the model vector space in order to treat the coordinate representative as already
`Function.IsSmoothOn`.  The project's `IsEmbeddedSubmanifold` owner likewise extends
`BoundarylessManifold`.  A source-with-boundary variant would need a Seeley extension of that
coordinate representative off `range J` and is not proved here. -/
theorem exists_local_vectorField_extension_of_isSmoothEmbedding
    [T2Space M] [SigmaCompactSpace M]
    [BoundarylessManifold J S]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) :
    ∃ U : TopologicalSpace.Opens M, ∃ hSU : (S : Set M) ⊆ U,
      ∃ Y : Cₛ^∞⟮I; E, fun p : U ↦ TangentSpace I p⟯,
        VectorField.f_related (fun p : S ↦ (⟨(p : M), hSU p.2⟩ : U)) X Y := by
  classical
  have hPointwise :
      ∀ p : S,
        ContMDiffVectorFieldLocalExtension
          (ambientSubtypePushforwardField X : ∀ p : S, TangentSpace I (p : M)) p := by
    intro p
    let V := Classical.choose (embeddedPointwiseLocalAmbientCoordinateExtension hS X p)
    have hVspec :=
      Classical.choose_spec (embeddedPointwiseLocalAmbientCoordinateExtension hS X p)
    have hV_open : IsOpen V := hVspec.1
    have hpV : (p : M) ∈ V := hVspec.2.1
    have hVbaseAndCoord := hVspec.2.2
    have hV_base :
        V ⊆ (trivializationAt E (TangentSpace I) (p : M)).baseSet := hVbaseAndCoord.1
    let χ := Classical.choose hVbaseAndCoord.2
    have hχspec := Classical.choose_spec hVbaseAndCoord.2
    have hχ : ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V := hχspec.1
    have hχ_eq :
        ∀ q : S, (q : M) ∈ V →
          χ q =
            (trivializationAt E (TangentSpace I) (p : M)
              ⟨(q : M), ambientSubtypePushforwardField X q⟩).2 := hχspec.2
    let τ := trivializationAt E (TangentSpace I) (p : M)
    let Xloc : ∀ y : M, TangentSpace I y := fun y ↦ τ.symm y (χ y)
    refine
      { V := V
        isOpen_V := hV_open
        mem_V := hpV
        Xloc := Xloc
        contMDiffOn := ?_
        eq_source := ?_ }
    · -- Rebuild the ambient field from its smooth trivialization coordinates on the chosen patch.
      simpa [τ, Xloc] using
        ambientFieldFromTrivializationCoordinates_contMDiffOn (p : M) hV_open hχ hV_base
    · intro q hqV
      -- On the submanifold patch, the rebuilt ambient field matches the prescribed pushforward.
      simpa [τ, Xloc] using
        (ambientFieldFromTrivializationCoordinates_eq_source (p : M) hV_base hχ_eq) q hqV
  obtain ⟨U, hSU, Y, hY⟩ :=
    exists_local_vectorField_extension_of_pointwiseLocalAmbientExtension
      (ambientSubtypePushforwardField X) hPointwise
  refine ⟨U, hSU, Y, ?_⟩
  refine ⟨subtypeValToNeighborhood_contMDiff hS hSU, ?_⟩
  intro p
  let f : S → U := fun q : S ↦ (⟨(q : M), hSU q.2⟩ : U)
  have hf :
      MDifferentiableAt J I f p := by
    -- The codomain-restricted inclusion is smooth, hence differentiable at `p`.
    exact (subtypeValToNeighborhood_contMDiff hS hSU).mdifferentiableAt (by simp)
  have hsub :
      MDifferentiableAt I I (Subtype.val : U → M) (f p) := by
    -- The open-subset inclusion is smooth at every point of `U`.
    exact
      (contMDiff_subtype_val : ContMDiff I I (∞ : ℕ∞ω) (Subtype.val : U → M)).mdifferentiableAt
        (by simp)
  -- Rewrite the target by the pullback normal form produced in the neighborhood gluing lemma.
  rw [hY p]
  rw [eq_comm, (mfderiv_open_subset_inclusion_isInvertible U (f p)).inverse_apply_eq]
  -- Differentiating `Subtype.val ∘ f = Subtype.val` recovers the ambient pushforward field.
  simpa [f, ambientSubtypePushforwardField, Function.comp] using!
    (mfderiv_comp_apply p hsub hf (X p))

section GlobalExtension

variable [T2Space M] [SigmaCompactSpace M]

/-- Helper for Problem 8-15: nonproper embeddedness yields a point of the ambient closure that does
not lie on the submanifold itself. -/
private lemma notProperlyEmbedded_exists_closure_witness
    (hNotProper : ¬ S.IsProperlyEmbedded) :
    ∃ r : M, r ∈ closure (S : Set M) ∧ r ∉ (S : Set M) := by
  classical
  have hNotClosed : ¬ IsClosed (S : Set M) := by
    -- In a Hausdorff ambient manifold, proper embeddedness is equivalent to closedness.
    intro hClosed
    exact hNotProper (Set.isProperlyEmbedded_iff_isClosed.2 hClosed)
  by_contra hNoWitness
  apply hNotClosed
  rw [← closure_eq_iff_isClosed]
  refine subset_antisymm ?_ subset_closure
  intro x hxClosure
  by_contra hxS
  exact hNoWitness ⟨x, hxClosure, hxS⟩

/-- From a missing closure point, select distinct source points converging to it, all inside the
base of the fixed ambient tangent-bundle trivialization at that point. -/
private lemma problem815_exists_injective_sequence_in_trivialization
    {r : M} (hrClosure : r ∈ closure (S : Set M)) (hrNotMem : r ∉ (S : Set M)) :
    ∃ p : ℕ → S,
      Function.Injective p ∧
        (∀ n, (p n : M) ∈ (trivializationAt E (TangentSpace I) r).baseSet) ∧
          Filter.Tendsto (fun n ↦ (p n : M)) Filter.atTop (𝓝 r) := by
  classical
  letI : SecondCountableTopology H := I.secondCountableTopology
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨q, hqS, hqLim⟩ := mem_closure_iff_seq_limit.mp hrClosure
  let qS : ℕ → S := fun n ↦ ⟨q n, hqS n⟩
  have hqSLim : Filter.Tendsto (fun n ↦ (qS n : M)) Filter.atTop (𝓝 r) := by
    simpa [qS] using hqLim
  have hqRangeInfinite : (Set.range qS).Infinite := by
    intro hfinite
    have hImageFinite : (Subtype.val '' Set.range qS : Set M).Finite :=
      hfinite.image Subtype.val
    have hrImage : r ∈ Subtype.val '' Set.range qS :=
      hImageFinite.isClosed.mem_of_tendsto hqSLim
        (Filter.Eventually.of_forall fun n ↦ ⟨qS n, Set.mem_range_self n, rfl⟩)
    rcases hrImage with ⟨x, -, hxr⟩
    exact hrNotMem (hxr ▸ x.2)
  have hRangeOutsideFinite :
      ∀ U : Set M, U ∈ 𝓝 r →
        (Set.range qS \ {x : S | (x : M) ∈ U}).Finite := by
    intro U hU
    have hEventually : ∀ᶠ n in Filter.atTop, (qS n : M) ∈ U := hqSLim.eventually hU
    have hEventuallyCofinite : ∀ᶠ n in Filter.cofinite, (qS n : M) ∈ U := by
      simpa only [Nat.cofinite_eq_atTop] using hEventually
    have hBadFinite : {n : ℕ | (qS n : M) ∉ U}.Finite :=
      Filter.eventually_cofinite.mp hEventuallyCofinite
    refine (hBadFinite.image qS).subset ?_
    intro x hx
    rcases hx.1 with ⟨n, rfl⟩
    exact ⟨n, hx.2, rfl⟩
  let τ := trivializationAt E (TangentSpace I) r
  let A : Set S := {x : S | (x : M) ∈ τ.baseSet} ∩ Set.range qS
  have hrτ : r ∈ τ.baseSet := FiberBundle.mem_baseSet_trivializationAt' r
  have hAInfinite : A.Infinite := by
    intro hAFinite
    have hOutsideFinite :
        (Set.range qS \ {x : S | (x : M) ∈ τ.baseSet}).Finite :=
      hRangeOutsideFinite τ.baseSet (τ.open_baseSet.mem_nhds hrτ)
    apply hqRangeInfinite
    refine (hAFinite.union hOutsideFinite).subset ?_
    intro x hx
    by_cases hxb : (x : M) ∈ τ.baseSet
    · exact Or.inl ⟨hxb, hx⟩
    · exact Or.inr ⟨hx, hxb⟩
  letI : Infinite A := Set.infinite_coe_iff.mpr hAInfinite
  let e : ℕ ↪ A := Infinite.natEmbedding A
  let p : ℕ → S := fun n ↦ e n
  have hpInjective : Function.Injective p := by
    intro m n hmn
    apply e.injective
    exact Subtype.ext hmn
  have hpBase : ∀ n, (p n : M) ∈ τ.baseSet := fun n ↦ (e n).property.1
  have hpLim : Filter.Tendsto (fun n ↦ (p n : M)) Filter.atTop (𝓝 r) := by
    rw [Filter.tendsto_def]
    intro U hU
    rw [← Nat.cofinite_eq_atTop, Filter.mem_cofinite]
    have hOutsideFinite := hRangeOutsideFinite U hU
    have hPreimageFinite :
        (p ⁻¹' (Set.range qS \ {x : S | (x : M) ∈ U})).Finite :=
      hOutsideFinite.preimage hpInjective.injOn
    refine hPreimageFinite.subset ?_
    intro n hn
    change (p n : M) ∉ U at hn
    exact ⟨(e n).property.2, hn⟩
  exact ⟨p, hpInjective, hpBase, hpLim⟩

/-- A sequence in the ambient manifold converging to a point outside `S` gives a locally finite
family of singleton subsets of `S`. -/
private lemma problem815_locallyFinite_singletons_of_tendsto_outside
    {r : M} (p : ℕ → S)
    (hpLim : Filter.Tendsto (fun n ↦ (p n : M)) Filter.atTop (𝓝 r))
    (hrNotMem : r ∉ (S : Set M)) :
    LocallyFinite (fun n ↦ ({p n} : Set S)) := by
  intro x
  have hxr : (x : M) ≠ r := fun h ↦ hrNotMem (h ▸ x.2)
  rcases t2_separation hxr with ⟨U, V, hUOpen, hVOpen, hxU, hrV, hUV⟩
  refine ⟨Subtype.val ⁻¹' U,
    (hUOpen.preimage continuous_subtype_val).mem_nhds hxU, ?_⟩
  have hEventually : ∀ᶠ n in Filter.atTop, (p n : M) ∈ V :=
    hpLim.eventually (hVOpen.mem_nhds hrV)
  have hEventuallyCofinite : ∀ᶠ n in Filter.cofinite, (p n : M) ∈ V := by
    simpa only [Nat.cofinite_eq_atTop] using hEventually
  have hBadFinite : {n : ℕ | (p n : M) ∉ V}.Finite :=
    Filter.eventually_cofinite.mp hEventuallyCofinite
  refine hBadFinite.subset ?_
  intro n hn
  rcases hn with ⟨y, hy, hyU⟩
  have hyEq : y = p n := by simpa using hy
  subst y
  have hypU : (p n : M) ∈ U := hyU
  have hypNotV : (p n : M) ∉ V := fun hpV ↦ Set.disjoint_left.1 hUV hypU hpV
  exact hypNotV

include I in
/-- Smoothly interpolate prescribed tangent vectors on a locally finite sequence of distinct
source points.  The construction uses constant coordinates in a tangent-bundle trivialization
near each selected point and the standard smooth-section partition-of-unity gluing theorem. -/
private lemma problem815_exists_smooth_vectorField_interpolating
    (p : ℕ → S) (hpInjective : Function.Injective p)
    (hpLocallyFinite : LocallyFinite (fun n ↦ ({p n} : Set S)))
    (v : ∀ n, TangentSpace J (p n)) :
    ∃ X : SmoothSubmanifoldVectorField, ∀ n, X (p n) = v n := by
  classical
  letI : SecondCountableTopology H := I.secondCountableTopology
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  letI : SecondCountableTopology S := inferInstance
  letI : LocallyCompactSpace H' := J.locallyCompactSpace
  letI : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace H' S
  letI : SigmaCompactSpace S := sigmaCompactSpace_of_locallyCompact_secondCountable
  let t : ∀ x : S, Set (TangentSpace J x) := fun x ↦
    {w | ∀ n (h : p n = x), w = h ▸ v n}
  have htConvex : ∀ x, Convex ℝ (t x) := by
    intro x
    rw [convex_iff_add_mem]
    intro a ha b hb α β hα hβ hsum
    intro n hn
    subst x
    rw [ha n rfl, hb n rfl, ← add_smul, hsum, one_smul]
  have hRangeClosed : IsClosed (Set.range p) := by
    rw [← Set.iUnion_singleton_eq_range]
    exact hpLocallyFinite.isClosed_iUnion fun _ ↦ isClosed_singleton
  have hLocal :
      ∀ x : S, ∃ U ∈ 𝓝 x, ∃ sLoc : ∀ y : S, TangentSpace J y,
        ContMDiffOn J J.tangent (∞ : ℕ∞ω) (T% sLoc) U ∧
          ∀ y ∈ U, sLoc y ∈ t y := by
    intro x
    by_cases hx : x ∈ Set.range p
    · rcases hx with ⟨n, rfl⟩
      let τ := trivializationAt E' (TangentSpace J) (p n)
      let c : E' := (τ ⟨p n, v n⟩).2
      let W : Set S := ⋂ m, ⋂ (_ : p n ∉ ({p m} : Set S)), ({p m} : Set S)ᶜ
      let U : Set S := τ.baseSet ∩ W
      let sLoc : ∀ y : S, TangentSpace J y := fun y ↦ τ.symm y c
      have hpτ : p n ∈ τ.baseSet := FiberBundle.mem_baseSet_trivializationAt' (p n)
      have hWnhds : W ∈ 𝓝 (p n) := by
        simpa [W] using
          hpLocallyFinite.iInter_compl_mem_nhds (fun _ ↦ isClosed_singleton) (p n)
      have hUnhds : U ∈ 𝓝 (p n) :=
        Filter.inter_mem (τ.open_baseSet.mem_nhds hpτ) hWnhds
      refine ⟨U, hUnhds, sLoc, ?_, ?_⟩
      · have hsBase :
            ContMDiffOn J J.tangent (∞ : ℕ∞ω) (T% sLoc) τ.baseSet := by
          apply (Bundle.Trivialization.contMDiffOn_section_baseSet_iff τ).2
          have hcSmooth :
              ContMDiffOn J 𝓘(ℝ, E') (∞ : ℕ∞ω) (fun _ : S ↦ c) τ.baseSet :=
            contMDiffOn_const
          refine hcSmooth.congr ?_
          intro y hy
          simpa [sLoc, c] using congrArg Prod.snd (τ.apply_mk_symm hy c)
        exact hsBase.mono fun _ hy ↦ hy.1
      · intro y hy
        intro m hmy
        have hmn : m = n := by
          by_contra hmne
          have hpnNot : p n ∉ ({p m} : Set S) := by
            simpa only [Set.mem_singleton_iff] using (hpInjective.ne hmne).symm
          have hyNot : y ∉ ({p m} : Set S) :=
            Set.mem_iInter₂.mp hy.2 m hpnNot
          exact hyNot (by simpa only [Set.mem_singleton_iff] using hmy.symm)
        subst m
        have hyn : y = p n := hmy.symm
        subst y
        simpa [sLoc, c] using τ.symm_apply_apply_mk hpτ (v n)
    · refine ⟨(Set.range p)ᶜ, hRangeClosed.isOpen_compl.mem_nhds hx,
        fun _ ↦ 0, ?_, ?_⟩
      · simpa using
          ((0 : SmoothSubmanifoldVectorField).contMDiff.contMDiffOn (s := (Set.range p)ᶜ))
      · intro y hy
        intro n hyn
        exact False.elim (hy ⟨n, hyn⟩)
  obtain ⟨X, hX⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local
      J (TangentSpace J) t htConvex hLocal
  refine ⟨X, ?_⟩
  intro n
  exact hX (p n) n rfl

/-- Helper for Problem 8-15: a positive-dimensional embedded submanifold which is not closed has
an intrinsic smooth vector field with no global ambient extension.  The field is assembled from
locally finite bumps at points `p n` converging to a missing closure point.  Only the selected
tangent vectors are normalized: in a fixed ambient tangent trivialization their pushforwards have
norm `n + 1`, so continuity rules out any ambient extension. -/
private lemma notProperlyEmbedded_exists_nonextendableVectorField
    [BoundarylessManifold J S]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (hpos : 0 < Module.finrank ℝ E')
    (hNotProper : ¬ S.IsProperlyEmbedded) :
    ∃ X : SmoothSubmanifoldVectorField,
      ¬ ∃ Z : SmoothAmbientVectorField,
        VectorField.f_related (Subtype.val : S → M) X Z := by
  classical
  rcases notProperlyEmbedded_exists_closure_witness hNotProper with
    ⟨r, hrClosure, hrNotMem⟩
  rcases problem815_exists_injective_sequence_in_trivialization
      (E := E) (I := I) (S := S) hrClosure hrNotMem with
    ⟨p, hpInjective, hpBase, hpTendsto⟩
  have hpLocallyFinite : LocallyFinite (fun n : ℕ ↦ ({p n} : Set S)) :=
    problem815_locallyFinite_singletons_of_tendsto_outside p hpTendsto hrNotMem
  rcases Module.finrank_pos_iff_exists_ne_zero.mp hpos with ⟨v₀, hv₀⟩
  let τ := trivializationAt E (TangentSpace I) r
  let L (n : ℕ) : TangentSpace I (p n : M) ≃L[ℝ] E :=
    τ.continuousLinearEquivAt ℝ (p n : M) (hpBase n)
  let u₀ (n : ℕ) : TangentSpace J (p n) :=
    (show TangentSpace J (p n) from v₀)
  let w (n : ℕ) : E :=
    L n (mfderiv J I (Subtype.val : S → M) (p n) (u₀ n))
  have hw_ne (n : ℕ) : w n ≠ 0 := by
    intro hw
    have hu : u₀ n = 0 := by
      apply isSmoothEmbedding_mfderiv_injective hS (p n)
      apply (L n).injective
      simpa [w] using hw
    exact hv₀ hu
  let a (n : ℕ) : ℝ := ((n : ℝ) + 1) / ‖w n‖
  let v (n : ℕ) : TangentSpace J (p n) := a n • u₀ n
  have hv_norm (n : ℕ) :
      ‖L n (mfderiv J I (Subtype.val : S → M) (p n) (v n))‖ =
        (n : ℝ) + 1 := by
    have hwNormPos : 0 < ‖w n‖ := norm_pos_iff.mpr (hw_ne n)
    have haNonneg : 0 ≤ a n :=
      (div_pos (by positivity : 0 < (n : ℝ) + 1) hwNormPos).le
    rw [show v n = a n • u₀ n from rfl, map_smul, (L n).map_smul, norm_smul]
    rw [Real.norm_of_nonneg haNonneg]
    change a n * ‖w n‖ = (n : ℝ) + 1
    exact div_mul_cancel₀ ((n : ℝ) + 1) (norm_ne_zero_iff.mpr (hw_ne n))
  rcases problem815_exists_smooth_vectorField_interpolating
      (I := I) (J := J) (S := S) p hpInjective hpLocallyFinite v with ⟨X, hX⟩
  refine ⟨X, ?_⟩
  rintro ⟨Z, hXZ⟩
  let zTotal : M → TangentBundle I M := fun x ↦ T% Z x
  have hzTotalTendsto :
      Filter.Tendsto (fun n ↦ zTotal (p n : M)) Filter.atTop (𝓝 (zTotal r)) :=
    Z.contMDiff.continuous.continuousAt.tendsto.comp hpTendsto
  have hrBase : r ∈ τ.baseSet := FiberBundle.mem_baseSet_trivializationAt' r
  have hrSource : zTotal r ∈ τ.source := τ.mem_source.mpr hrBase
  have hpSource : ∀ n, zTotal (p n : M) ∈ τ.source := fun n ↦
    τ.mem_source.mpr (hpBase n)
  have hzWithin : Filter.Tendsto (fun n ↦ zTotal (p n : M)) Filter.atTop
      (𝓝[τ.source] (zTotal r)) :=
    tendsto_nhdsWithin_iff.2 ⟨hzTotalTendsto, Filter.Eventually.of_forall hpSource⟩
  have hτTendsto :
      Filter.Tendsto (fun n ↦ τ (zTotal (p n : M))) Filter.atTop
        (𝓝 (τ (zTotal r))) :=
    τ.continuousOn (zTotal r) hrSource |>.tendsto.comp hzWithin
  have hCoordTendsto :
      Filter.Tendsto (fun n ↦ (τ (zTotal (p n : M))).2) Filter.atTop
        (𝓝 (τ (zTotal r)).2) :=
    continuous_snd.continuousAt.tendsto.comp hτTendsto
  have hNormTendsto :
      Filter.Tendsto (fun n ↦ ‖(τ (zTotal (p n : M))).2‖) Filter.atTop
        (𝓝 ‖(τ (zTotal r)).2‖) :=
    hCoordTendsto.norm
  have hBound :
      ∀ᶠ n in Filter.atTop,
        ‖(τ (zTotal (p n : M))).2‖ < ‖(τ (zTotal r)).2‖ + 1 :=
    hNormTendsto.eventually (Iio_mem_nhds (by linarith))
  have hCoordNorm (n : ℕ) :
      ‖(τ (zTotal (p n : M))).2‖ = (n : ℝ) + 1 := by
    rw [show zTotal (p n : M) =
        ⟨(p n : M), Z (p n : M)⟩ from rfl]
    rw [← hXZ.2 (p n), hX n]
    simpa [L] using hv_norm n
  rcases Filter.eventually_atTop.1 hBound with ⟨N, hN⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (‖(τ (zTotal r)).2‖ + 1)
  let n := max N k
  have hnBound := hN n (le_max_left N k)
  rw [hCoordNorm n] at hnBound
  have hkn : (k : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_max_right N k
  linarith

/-- Problem 8-15 (2), forward direction: if the boundaryless embedded submanifold `S` is properly
embedded, then every intrinsic smooth vector field on `S` extends to a globally defined smooth
ambient vector field on `M`.  This packages the local extension theorem from part (1) with the
closed-subset extension lemma.

As in part (1), the source is required to be boundaryless.  The general source-with-boundary
forward statement depends on a Seeley extension of the chart representative and is not claimed. -/
theorem exists_global_vectorField_extension_of_isProperlyEmbedded
    [BoundarylessManifold J S]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (hProper : S.IsProperlyEmbedded)
    (X : SmoothSubmanifoldVectorField) :
    ∃ Z : SmoothAmbientVectorField,
      VectorField.f_related (Subtype.val : S → M) X Z := by
  classical
  have hPointwise :
      ∀ p : S,
        ContMDiffVectorFieldLocalExtension
          (ambientSubtypePushforwardField X : ∀ p : S, TangentSpace I (p : M)) p := by
    intro p
    let V := Classical.choose (embeddedPointwiseLocalAmbientCoordinateExtension hS X p)
    have hVspec :=
      Classical.choose_spec (embeddedPointwiseLocalAmbientCoordinateExtension hS X p)
    have hV_open : IsOpen V := hVspec.1
    have hpV : (p : M) ∈ V := hVspec.2.1
    have hVbaseAndCoord := hVspec.2.2
    have hV_base :
        V ⊆ (trivializationAt E (TangentSpace I) (p : M)).baseSet := hVbaseAndCoord.1
    let χ := Classical.choose hVbaseAndCoord.2
    have hχspec := Classical.choose_spec hVbaseAndCoord.2
    have hχ : ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V := hχspec.1
    have hχ_eq :
        ∀ q : S, (q : M) ∈ V →
          χ q =
            (trivializationAt E (TangentSpace I) (p : M)
              ⟨(q : M), ambientSubtypePushforwardField X q⟩).2 := hχspec.2
    let τ := trivializationAt E (TangentSpace I) (p : M)
    let Xloc : ∀ y : M, TangentSpace I y := fun y ↦ τ.symm y (χ y)
    refine
      { V := V
        isOpen_V := hV_open
        mem_V := hpV
        Xloc := Xloc
        contMDiffOn := ?_
        eq_source := ?_ }
    · -- Rebuild the ambient field from the chosen smooth coordinate representative.
      simpa [τ, Xloc] using
        ambientFieldFromTrivializationCoordinates_contMDiffOn (p : M) hV_open hχ hV_base
    · intro q hqV
      -- The rebuilt field agrees with the pushed-forward source field on the submanifold patch.
      simpa [τ, Xloc] using
        (ambientFieldFromTrivializationCoordinates_eq_source (p : M) hV_base hχ_eq) q hqV
  exact
    properlyEmbedded_vectorField_globalExtension_of_pointwiseLocalAmbientExtension
      hS hProper X hPointwise

/-- Problem 8-15 (2), corrected formulation.  A neighborhood representative `Y` is used only to
witness the germ of the intrinsic field `X` along `S`; the global field is required to extend `X`
along `S`, not to agree with `Y` at every point of its whole (possibly nonclosed) domain.  The
latter, stronger statement is false: take `M = ℝ`, `S = {0}`, `U = (-1, 1)`, and the local field
with coefficient `x / (1 - x ^ 2)`, which cannot agree on all of `U` with a global smooth field.

For the converse, positive source dimension supplies a nonzero tangent vector at each selected
point of a sequence converging to a missing closure point.  Locally finite smooth bumps interpolate
vectors whose ambient trivialization coordinates diverge, contradicting continuity of a putative
global extension.

The source-boundaryless restriction is inherited from the local extension theorem used on the
converse side and from the interior-point construction of a local left inverse to the inclusion.
It is not a silent strengthening of Lee's ordinary-manifold statement: a source-with-boundary
variant remains a separate Seeley-extension dependency and is not proved here. -/
theorem exists_global_vectorField_extension_iff_isProperlyEmbedded
    [BoundarylessManifold J S]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (hpos : 0 < Module.finrank ℝ E') :
    (∀ (U : TopologicalSpace.Opens M) (hSU : (S : Set M) ⊆ U)
        (Y : Cₛ^∞⟮I; E, fun p : U ↦ TangentSpace I p⟯)
        (X : SmoothSubmanifoldVectorField),
        VectorField.f_related (fun p : S ↦ (⟨(p : M), hSU p.2⟩ : U)) X Y →
        ∃ Z : SmoothAmbientVectorField,
          VectorField.f_related (Subtype.val : S → M) X Z) ↔
      S.IsProperlyEmbedded := by
  constructor
  · intro hExtension
    by_contra hNotProper
    rcases notProperlyEmbedded_exists_nonextendableVectorField
        hS hpos hNotProper with ⟨X, hX⟩
    rcases exists_local_vectorField_extension_of_isSmoothEmbedding hS X with
      ⟨U, hSU, Y, hXY⟩
    exact hX (hExtension U hSU Y X hXY)
  · intro hProper U hSU Y X hXY
    exact exists_global_vectorField_extension_of_isProperlyEmbedded hS hProper X

/-- Companion for Problem 8-15 (2): quantifying directly over intrinsic vector fields.  Positive
dimension is exactly what permits the converse's pointwise tangent-vector spikes.  In dimension
`0`, every intrinsic vector field is zero, so this criterion cannot characterize proper
embeddedness.

As in the neighborhood-representative formulation, the source is required to be boundaryless.
The general boundary-source case is not claimed. -/
theorem exists_global_vectorField_extension_iff_isProperlyEmbedded_of_posDim
    [BoundarylessManifold J S]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (hpos : 0 < Module.finrank ℝ E') :
    (∀ X : SmoothSubmanifoldVectorField,
      ∃ Z : SmoothAmbientVectorField,
        VectorField.f_related (Subtype.val : S → M) X Z) ↔
      S.IsProperlyEmbedded := by
  constructor
  · intro hExtension
    by_contra hNotProper
    rcases notProperlyEmbedded_exists_nonextendableVectorField
        hS hpos hNotProper with ⟨X, hX⟩
    exact hX (hExtension X)
  · intro hProper X
    exact exists_global_vectorField_extension_of_isProperlyEmbedded hS hProper X

#print axioms exists_local_vectorField_extension_of_isSmoothEmbedding
#print axioms exists_global_vectorField_extension_of_isProperlyEmbedded
#print axioms exists_global_vectorField_extension_iff_isProperlyEmbedded
#print axioms exists_global_vectorField_extension_iff_isProperlyEmbedded_of_posDim

end GlobalExtension

end
