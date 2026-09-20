import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Compactness.Compact
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch04.Sec04_21.Proposition_4_1
import LeeSmoothLib.Ch04.Sec04_24.Proposition_4_22
import LeeSmoothLib.Ch04.Sec04_24.Theorem_4_25
import LeeSmoothLib.Ch04.Sec04_25.Proposition_4_28
import LeeSmoothLib.Ch05.Sec05_32.Definition_5_32_extra_2
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_2
import LeeSmoothLib.Ch05.Sec05_33.Theorem_5_33
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_38
import LeeSmoothLib.Ch05.Sec05_37.Problem_5_7
import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_1
import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_2
import LeeSmoothLib.Ch06.Sec06_45.StableMapClass
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Set Manifold
open Topology.IsInducing

local notation "𝕜" => ℝ

universe u𝕜 uE uE' uH uH' uN uM uS uES uHS

namespace Theorem630.LevelSetOn

section Problem616Local

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ N] [BoundarylessManifold I N]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ M] [BoundarylessManifold J M]


omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: for a surjective continuous linear map `B`, surjectivity of
`B.comp A` is equivalent to `A.range ⊔ B.ker = ⊤`. -/
lemma surjectiveComp_iff_range_sup_ker_eq_top
    {V W Z : Type _}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {A : V →L[𝕜] W} {B : W →L[𝕜] Z} (hB : Function.Surjective B) :
    Function.Surjective (B.comp A) ↔ A.range ⊔ B.ker = ⊤ := by
  -- Reduce the spanning condition to the standard surjectivity criterion for the restriction of
  -- `B` to the image of `A`.
  have hdom :
      Function.Surjective (B.toLinearMap.domRestrict A.range) ↔
        A.range ⊔ B.ker = ⊤ := by
    simpa only [codisjoint_iff] using (LinearMap.surjective_domRestrict_iff hB)
  constructor
  · intro hComp
    -- A preimage for `B ∘ A` immediately gives a preimage for the domain restriction of `B`.
    exact hdom.mp <| by
      intro z
      rcases hComp z with ⟨x, rfl⟩
      exact ⟨⟨A x, ⟨x, rfl⟩⟩, rfl⟩
  · intro hSup
    -- Conversely, surjectivity on the restricted range lifts back through the witness `A x`.
    have hDomSurj : Function.Surjective (B.toLinearMap.domRestrict A.range) :=
      hdom.mpr hSup
    intro z
    rcases hDomSurj z with ⟨y, hy⟩
    rcases y.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change B (A x) = z
    exact hx ▸ hy

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: after lowering the subtype immersion to the current `∞`
owner, the
front projection of the immersion normal form recovers the intrinsic source coordinates. -/
lemma immersionProjectionEqDomainCoordinatesInf
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] {JX : ModelWithCorners 𝕜 EX HX}
    [ChartedSpace HX X] [IsManifold JX ∞ X]
    {p q : X}
    (hImm : Manifold.IsImmersionAt JX J ∞ (Subtype.val : X → M) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E' →L[𝕜] EX :=
      let equivSymm := hImm.equiv.symm
      let eSymm := equivSymm.toContinuousLinearMap
      (ContinuousLinearMap.fst 𝕜 EX hImm.complement).comp eSymm
    π ((hImm.codChart.extend J) q) = (hImm.domChart.extend JX) q := by
  let equivSymm := hImm.equiv.symm
  let eSymm := equivSymm.toContinuousLinearMap
  let π : E' →L[𝕜] EX :=
    (ContinuousLinearMap.fst 𝕜 EX hImm.complement).comp eSymm
  have hq_source : q ∈ (hImm.domChart.extend JX).source := by
    simpa [hImm.domChart.extend_source] using hq
  have hq_target : (hImm.domChart.extend JX) q ∈ (hImm.domChart.extend JX).target :=
    (hImm.domChart.extend JX).map_source hq_source
  have hcoords := congrArg π (hImm.writtenInCharts hq_target)
  -- Apply the front projection to the immersion chart normal form and simplify the chart inverses.
  simpa [equivSymm, eSymm, π, Function.comp, ContinuousLinearMap.comp_apply,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, hq] using hcoords

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: the inverse of an extended maximal-atlas chart is differentiable
within the range of the model map. -/
lemma chartExtend_symm_mdifferentiableWithin_range
    {e : OpenPartialHomeomorph M H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ M) {p : M} (hp : p ∈ e.source) :
    MDifferentiableWithinAt 𝓘(𝕜, E') J (e.extend J).symm (Set.range J)
      (e.extend J p) := by
  letI : IsManifold J 1 M := IsManifold.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have he_one : e ∈ IsManifold.maximalAtlas J 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) he
  have hid :
      MDifferentiableWithinAt J J (id : M → M) Set.univ p := by
    -- The inverse-chart differentiability comes from rewriting the identity map in chart
    -- coordinates.
    simpa using
      (mdifferentiableWithinAt_id :
        MDifferentiableWithinAt J J (id : M → M) Set.univ p)
  have hiff :
      MDifferentiableWithinAt J J (id : M → M) Set.univ p ↔
        MDifferentiableWithinAt 𝓘(𝕜, E') J ((id : M → M) ∘ (e.extend J).symm)
          ((e.extend J).symm ⁻¹' Set.univ ∩ Set.range J) (e.extend J p) :=
    mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas he_one hp
  simpa [Function.comp] using hiff.mp hid

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: differentiating the chart left-inverse identity on the chart source
produces a concrete left inverse for the derivative of an extended maximal-atlas chart. -/
lemma chartExtend_mfderiv_left_inverse
    {e : OpenPartialHomeomorph M H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ M) {p : M} (hp : p ∈ e.source) :
    (mfderivWithin 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p)).comp
      (mfderiv J 𝓘(𝕜, E') (e.extend J) p) =
      ContinuousLinearMap.id 𝕜 (TangentSpace J p) := by
  letI : IsManifold J 1 M := IsManifold.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have he_one : e ∈ IsManifold.maximalAtlas J 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) he
  have hsource_unique : UniqueMDiffWithinAt J e.source p :=
    e.open_source.uniqueMDiffWithinAt hp
  have hchart :
      MDifferentiableAt J 𝓘(𝕜, E') (e.extend J) p := by
    -- Maximal-atlas charts are differentiable at every source point.
    exact
      (OpenPartialHomeomorph.contMDiffAt_extend he_one hp).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hrange :
      MDifferentiableWithinAt 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p) :=
    chartExtend_symm_mdifferentiableWithin_range he hp
  have hchart_within :
      mfderiv J 𝓘(𝕜, E') (e.extend J) p =
        mfderivWithin J 𝓘(𝕜, E') (e.extend J) e.source p := by
    -- On the open chart source, the within derivative agrees with the ordinary derivative.
    symm
    exact mfderivWithin_eq_mfderiv hsource_unique hchart
  rw [hchart_within, ← mfderivWithin_comp_of_eq]
  · -- Differentiate the left-inverse identity on the chart source where `UniqueMDiffWithinAt`
    -- is available.
    rw [← mfderivWithin_id hsource_unique]
    apply Filter.EventuallyEq.mfderivWithin_eq_of_mem
    · refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
      intro z hz
      simpa [Function.comp] using
        (show (e.extend J).symm (e.extend J z) = z from e.extend_left_inv hz)
    · exact hp
  · exact hrange
  · exact hchart.mdifferentiableWithinAt
  · intro z hz
    have hz_target : e.extend J z ∈ (e.extend J).target :=
      (e.extend J).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hz
    exact e.extend_target_subset_range hz_target
  · exact hsource_unique
  · rfl

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: the derivative of an extended maximal-atlas chart is injective on
its chart source. -/
lemma chartExtend_mfderiv_injective
    {e : OpenPartialHomeomorph M H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ M) {p : M} (hp : p ∈ e.source) :
    Function.Injective (mfderiv J 𝓘(𝕜, E') (e.extend J) p) := by
  let Linv :=
    mfderivWithin 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p)
  intro w₁ w₂ hw
  have hleft := chartExtend_mfderiv_left_inverse he hp
  have hp_left : (e.extend J).symm (e.extend J p) = p :=
    e.extend_left_inv hp
  have hw_push : Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₁) =
      Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₂) := by
    simpa [Linv] using congrArg Linv hw
  have hw₁ :
      Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₁) = w₁ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using!
      congrArg (fun L ↦ L w₁) hleft
  have hw₂ :
      Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using!
      congrArg (fun L ↦ L w₂) hleft
  -- Apply the derivative-level left inverse to both chart-coordinate tangent vectors.
  exact hw₁.symm.trans (hw_push.trans hw₂)

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: the derivative of an extended maximal-atlas chart is surjective on
its chart source because the domain and codomain tangent spaces have the same finite rank. -/
lemma chartExtend_mfderiv_surjective
    {e : OpenPartialHomeomorph M H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ M) {p : M} (hp : p ∈ e.source) :
    Function.Surjective (mfderiv J 𝓘(𝕜, E') (e.extend J) p) := by
  let A := (mfderiv J 𝓘(𝕜, E') (e.extend J) p).toLinearMap
  letI : FiniteDimensional 𝕜 (TangentSpace J p) := by
    change FiniteDimensional 𝕜 E'
    infer_instance
  letI : FiniteDimensional 𝕜 (TangentSpace 𝓘(𝕜, E') (e.extend J p)) := by
    change FiniteDimensional 𝕜 E'
    infer_instance
  have hfinrank :
      Module.finrank 𝕜 (TangentSpace J p) =
        Module.finrank 𝕜 (TangentSpace 𝓘(𝕜, E') (e.extend J p)) := by
    change Module.finrank 𝕜 E' = Module.finrank 𝕜 E'
    rfl
  have hAinj : Function.Injective A :=
    chartExtend_mfderiv_injective he hp
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp hAinj

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: an embedded submanifold is locally cut out by the complement
coordinates coming from an immersion normal form, and these complement coordinates already form a
local defining map. -/
lemma immersionComplementCoordinates_levelSetOn
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] (JX : ModelWithCorners 𝕜 EX HX)
    [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold J JX X]
    (x : X) :
    ∃ (K : Type uE') (_ : NormedAddCommGroup K) (_ : NormedSpace 𝕜 K)
      (_ : FiniteDimensional 𝕜 K) (U : Set M) (Φ : M → K),
      (x : M) ∈ U ∧
        IsLocalDefiningMapOn J 𝓘(𝕜, K) X U Φ ∧
        Module.finrank 𝕜 EX + Module.finrank 𝕜 K = Module.finrank 𝕜 E' := by
  let hSubtype : IsSmoothEmbedding JX J ∞ ((↑) : X → M) := by
    -- Lower the canonical embedded-submanifold inclusion to the `∞` owner used here.
    exact
      isSmoothEmbedding_of_le (by simp)
        (show IsSmoothEmbedding JX J (⊤ : WithTop ℕ∞) ((↑) : X → M) from
          IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val)
  let hImm : Manifold.IsImmersionAt JX J ∞ (Subtype.val : X → M) x :=
    hSubtype.isImmersion.isImmersionAt x
  let K := hImm.complement
  letI : FiniteDimensional 𝕜 (EX × K) :=
    FiniteDimensional.of_injective hImm.equiv.toLinearMap hImm.equiv.injective
  letI : FiniteDimensional 𝕜 EX := by
    exact
      FiniteDimensional.of_injective
        (ContinuousLinearMap.inl 𝕜 EX K).toLinearMap
        (by
          intro u v huv
          exact congrArg Prod.fst huv)
  letI : FiniteDimensional 𝕜 K := by
    exact
      FiniteDimensional.of_injective
        (ContinuousLinearMap.inr 𝕜 EX K).toLinearMap
        (by
          intro u v huv
          exact congrArg Prod.snd huv)
  have hcodim :
      Module.finrank 𝕜 EX + Module.finrank 𝕜 K = Module.finrank 𝕜 E' := by
    have hsum :
        Module.finrank 𝕜 (EX × K) =
          Module.finrank 𝕜 EX + Module.finrank 𝕜 K :=
      Module.finrank_prod
    have heq : Module.finrank 𝕜 (EX × K) = Module.finrank 𝕜 E' :=
      hImm.equiv.toLinearEquiv.finrank_eq
    exact hsum.symm.trans heq
  let front : E' →L[𝕜] EX :=
    (ContinuousLinearMap.fst 𝕜 EX K).comp hImm.equiv.symm.toContinuousLinearMap
  let tail : E' →L[𝕜] K :=
    (ContinuousLinearMap.snd 𝕜 EX K).comp hImm.equiv.symm.toContinuousLinearMap
  let Φ : M → K := tail ∘ (hImm.codChart.extend J)
  -- Use the same ambient patch as the local-section construction: stay in the codomain chart and
  -- force the projected first coordinates into the intrinsic source-chart target.
  rcases subtypeVal.isOpen_iff.mp hImm.domChart.open_source with
    ⟨W, hWOpen, hW_eq⟩
  let T : Set EX := interior ((hImm.domChart.extend JX).target)
  have hT_sub : T ⊆ (hImm.domChart.extend JX).target := interior_subset
  have hxW : (x : M) ∈ W := by
    have hx_pre : x ∈ Subtype.val ⁻¹' W := by
      rw [hW_eq]
      exact hImm.mem_domChart_source
    exact hx_pre
  have hxT : (hImm.domChart.extend JX) x ∈ T := by
    have hInteriorPoint :
        JX.IsInteriorPoint x ↔
          (hImm.domChart.extend JX) x ∈ interior ((hImm.domChart.extend JX).target) :=
      JX.isInteriorPoint_iff_of_mem_maximalAtlas
        (show (∞ : ℕ∞ω) ≠ 0 by simp)
        hImm.domChart_mem_maximalAtlas hImm.mem_domChart_source
    exact hInteriorPoint.1 BoundarylessManifold.isInteriorPoint
  have hxProj :
      front ((hImm.codChart.extend J) x) = (hImm.domChart.extend JX) x :=
    immersionProjectionEqDomainCoordinatesInf hImm hImm.mem_domChart_source
  have hxProjT : (front ∘ (hImm.codChart.extend J)) (x : M) ∈ T := by
    have hxComp :
        (front ∘ (hImm.codChart.extend J)) (x : M) = (hImm.domChart.extend JX) x := by
      simpa [Function.comp] using hxProj
    rw [hxComp]
    exact hxT
  have hFrontCont :
      ContinuousAt (front ∘ (hImm.codChart.extend J)) (x : M) := by
    exact front.continuous.continuousAt.comp
      (hImm.codChart.continuousAt_extend hImm.mem_codChart_source)
  have hPreT :
      ((front ∘ (hImm.codChart.extend J)) ⁻¹' T) ∈ nhds (x : M) := by
    exact hFrontCont.preimage_mem_nhds (isOpen_interior.mem_nhds hxProjT)
  rcases mem_nhds_iff.mp hPreT with ⟨V₀, hV₀_sub, hV₀_open, hxV₀⟩
  let U : Set M := hImm.codChart.source ∩ (W ∩ V₀)
  have hUOpen : IsOpen U := hImm.codChart.open_source.inter (hWOpen.inter hV₀_open)
  have hxU : (x : M) ∈ U := ⟨hImm.mem_codChart_source, hxW, hxV₀⟩
  have hU_cod : U ⊆ hImm.codChart.source := fun _ hx ↦ hx.1
  have hFrontTarget :
      ∀ q ∈ U, front ((hImm.codChart.extend J) q) ∈ (hImm.domChart.extend JX).target := by
    intro q hq
    exact hT_sub (hV₀_sub hq.2.2)
  have hDomChart_of_mem :
      ∀ {q : M} (hqX : q ∈ X), q ∈ U → (⟨q, hqX⟩ : X) ∈ hImm.domChart.source := by
    intro q hqX hqU
    have hqPre : (⟨q, hqX⟩ : X) ∈ Subtype.val ⁻¹' W := hqU.2.1
    rwa [hW_eq] at hqPre
  have hPhi_eq_zero_of_mem :
      ∀ {q : M}, q ∈ X → q ∈ U → Φ q = 0 := by
    intro q hqX hqU
    let qX : X := ⟨q, hqX⟩
    have hqDom : qX ∈ hImm.domChart.source :=
      hDomChart_of_mem hqX hqU
    have hqDomExt : qX ∈ (hImm.domChart.extend JX).source := by
      simpa [hImm.domChart.extend_source] using hqDom
    have hqTarget :
        (hImm.domChart.extend JX) qX ∈ (hImm.domChart.extend JX).target :=
      (hImm.domChart.extend JX).map_source hqDomExt
    -- On points of the submanifold, the complement coordinates in the immersion normal form vanish.
    have hcoords := congrArg tail (hImm.writtenInCharts hqTarget)
    simp only [Function.comp_apply] at hcoords
    rw [(hImm.domChart.extend JX).left_inv hqDomExt] at hcoords
    have hzero :
        tail (hImm.equiv ((hImm.domChart.extend JX) qX, (0 : K))) = 0 := by
      change
        (hImm.equiv.symm
          (hImm.equiv ((hImm.domChart.extend JX) qX, (0 : K)))).2 = 0
      rw [hImm.equiv.symm_apply_apply]
    change tail ((hImm.codChart.extend J) q) = 0
    simpa [qX] using hcoords.trans hzero
  have hMem_of_phi_eq_zero :
      ∀ {q : M}, q ∈ U → Φ q = 0 → q ∈ X := by
    intro q hqU hqPhi
    let qFront : EX := front ((hImm.codChart.extend J) q)
    have hqFrontTarget : qFront ∈ (hImm.domChart.extend JX).target :=
      hFrontTarget q hqU
    let qX : X := (hImm.domChart.extend JX).symm qFront
    have hqXChart :
        (hImm.domChart.extend JX) qX = qFront := by
      exact (hImm.domChart.extend JX).right_inv hqFrontTarget
    have hqXDom :
        qX ∈ hImm.domChart.source := by
      have hqXDomExt : qX ∈ (hImm.domChart.extend JX).source := by
        simpa [OpenPartialHomeomorph.extend_source] using!
          (hImm.domChart.extend JX).map_target hqFrontTarget
      simpa [hImm.domChart.extend_source] using hqXDomExt
    have hqXCod : ((qX : X) : M) ∈ hImm.codChart.source :=
      hImm.source_subset_preimage_source hqXDom
    have hqXTarget :
        (hImm.domChart.extend JX) qX ∈ (hImm.domChart.extend JX).target :=
      (hImm.domChart.extend JX).map_source <| by
        simpa [hImm.domChart.extend_source] using hqXDom
    have hqXCoords :
        (hImm.codChart.extend J) (qX : X) = hImm.equiv (qFront, (0 : K)) := by
      have hWritten := hImm.writtenInCharts hqXTarget
      have hLeftCoord :
          ((hImm.codChart.extend J) ∘ Subtype.val ∘ (hImm.domChart.extend JX).symm)
              ((hImm.domChart.extend JX) qX) =
            (hImm.codChart.extend J) (qX : X) := by
        simpa [Function.comp] using
          congrArg (fun z : X ↦ (hImm.codChart.extend J) (z : X))
            (hImm.domChart.extend_left_inv (I := JX) hqXDom)
      calc
        (hImm.codChart.extend J) (qX : X) =
            ((hImm.codChart.extend J) ∘ Subtype.val ∘ (hImm.domChart.extend JX).symm)
              ((hImm.domChart.extend JX) qX) := hLeftCoord.symm
        _ = hImm.equiv ((hImm.domChart.extend JX) qX, (0 : K)) := hWritten
        _ = hImm.equiv (qFront, (0 : K)) := by rw [hqXChart]
    have hqCoords :
        (hImm.codChart.extend J) q = hImm.equiv (qFront, (0 : K)) := by
      have hSymmEq :
          hImm.equiv.symm ((hImm.codChart.extend J) q) = (qFront, (0 : K)) := by
        apply Prod.ext
        · rfl
        · simpa [Φ, qFront, tail, front, Function.comp, ContinuousLinearMap.comp_apply] using! hqPhi
      calc
        (hImm.codChart.extend J) q =
            hImm.equiv (hImm.equiv.symm ((hImm.codChart.extend J) q)) := by
              simpa using (hImm.equiv.apply_symm_apply ((hImm.codChart.extend J) q)).symm
        _ = hImm.equiv (qFront, (0 : K)) := by rw [hSymmEq]
    have hqCod : q ∈ hImm.codChart.source := hU_cod hqU
    have hEqExt :
        (hImm.codChart.extend J) q = (hImm.codChart.extend J) (qX : X) :=
      hqCoords.trans hqXCoords.symm
    have hEq : q = (qX : X) := by
      calc
        q = (hImm.codChart.extend J).symm ((hImm.codChart.extend J) q) := by
          symm
          exact hImm.codChart.extend_left_inv hqCod
        _ = (hImm.codChart.extend J).symm ((hImm.codChart.extend J) (qX : X)) := by
          rw [hEqExt]
        _ = (qX : X) := by
          exact hImm.codChart.extend_left_inv hqXCod
    exact hEq ▸ qX.2
  refine ⟨K, inferInstance, inferInstance, inferInstance, U, Φ, hxU, ?_, hcodim⟩
  refine
    { isOpen_source := hUOpen
      smoothOn := ?_
      mem_iff_eq := ?_
      surjective_mfderiv := ?_ }
  · -- The complement-coordinate map is a linear projection of the ambient chart coordinates.
    have hChartSmooth :
        ContMDiffOn J 𝓘(𝕜, E') ∞ (hImm.codChart.extend J) U := by
      exact (OpenPartialHomeomorph.contMDiffOn_extend
        hImm.codChart_mem_maximalAtlas).mono hU_cod
    simpa [Φ, Function.comp] using tail.contDiff.contMDiff.comp_contMDiffOn hChartSmooth
  · intro p q hpX hpU hqU
    have hpZero : Φ p = 0 := hPhi_eq_zero_of_mem hpX hpU
    constructor
    · intro hqX
      simpa [hpZero] using hPhi_eq_zero_of_mem hqX hqU
    · intro hEq
      exact hMem_of_phi_eq_zero hqU (by simpa [hpZero] using hEq)
  · intro p hpU
    have hpCod : p ∈ hImm.codChart.source := hU_cod hpU
    have hChartDiff :
        MDifferentiableAt J 𝓘(𝕜, E') (hImm.codChart.extend J) p := by
      exact
        (OpenPartialHomeomorph.contMDiffAt_extend
          hImm.codChart_mem_maximalAtlas hpCod).mdifferentiableAt
          (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hTailDiff :
        MDifferentiableAt 𝓘(𝕜, E') 𝓘(𝕜, K) tail ((hImm.codChart.extend J) p) := by
      simpa [tail] using tail.contDiff.contMDiff.mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hTailSurj : Function.Surjective tail := by
      intro k
      refine ⟨hImm.equiv (0, k), ?_⟩
      change (hImm.equiv.symm (hImm.equiv (0, k))).2 = k
      rw [hImm.equiv.symm_apply_apply]
    have hChartSurj :
        Function.Surjective (mfderiv J 𝓘(𝕜, E') (hImm.codChart.extend J) p) :=
      chartExtend_mfderiv_surjective hImm.codChart_mem_maximalAtlas hpCod
    have hmf :
        mfderiv J 𝓘(𝕜, K) Φ p =
          tail.comp (mfderiv J 𝓘(𝕜, E') (hImm.codChart.extend J) p) := by
      rw [show Φ = tail ∘ (hImm.codChart.extend J) by rfl]
      rw [mfderiv_comp p hTailDiff hChartDiff, ContinuousLinearMap.mfderiv_eq]
    rw [hmf]
    exact hTailSurj.comp hChartSurj

end Problem616Local

end Theorem630.LevelSetOn
