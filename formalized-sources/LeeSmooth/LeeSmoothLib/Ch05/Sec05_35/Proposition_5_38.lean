import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import LeeSmoothLib.Ch05.Sec05_35.Notation_5_35_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold Topology

set_option backward.isDefEq.respectTransparency false

section SubmanifoldTangentSpace

universe u𝕜 uE uE' uF uH uH' uG uM uN

open Manifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {G : Type uG} [TopologicalSpace G]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S]
variable {K : ModelWithCorners 𝕜 F G} [IsManifold K ∞ N]

/-- A local defining map on `U` cuts out `S` as the fiber through each point of `S ∩ U` and has
surjective differential on `U`. -/
structure IsLocalDefiningMapOn (I : ModelWithCorners 𝕜 E H) (K : ModelWithCorners 𝕜 F G)
    (S U : Set M) (Φ : M → N) : Prop where
  isOpen_source : IsOpen U
  smoothOn : ContMDiffOn I K ∞ Φ U
  mem_iff_eq {p q : M} : p ∈ S → p ∈ U → q ∈ U → (q ∈ S ↔ Φ q = Φ p)
  surjective_mfderiv {p : M} : p ∈ U → Function.Surjective (mfderiv I K Φ p)

omit [IsManifold I ∞ M] in
/-- The derivative of an extended maximal-atlas chart has a left inverse, also for models with
corners.  This is the chart-level cancellation needed below; it does not use a boundaryless
model assumption. -/
private lemma mfderivWithin_extend_symm_comp_mfderiv_extend_538
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) :
    (mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (Set.range I) (e.extend I x)) ∘L
      (mfderiv I 𝓘(𝕜, E) (e.extend I) x) =
        ContinuousLinearMap.id 𝕜 _ := by
  have hx_source : x ∈ (e.extend I).source := by
    simpa [e.extend_source (I := I)] using hx
  have hy : e.extend I x ∈ (e.extend I).target := (e.extend I).map_source hx_source
  have hsource_unique : UniqueMDiffWithinAt I (e.extend I).source x :=
    (e.isOpen_extend_source (I := I)).uniqueMDiffWithinAt hx_source
  have hchart : MDifferentiableAt I 𝓘(𝕜, E) (e.extend I) x :=
    (e.contMDiffAt_extend he hx).mdifferentiableAt (by simp)
  have hinv :
      MDifferentiableWithinAt 𝓘(𝕜, E) I (e.extend I).symm (Set.range I)
        (e.extend I x) := by
    have hI : MDifferentiableWithinAt 𝓘(𝕜, E) I I.symm (Set.range I)
        (e.extend I x) :=
      I.mdifferentiableWithinAt_symm (e.extend_target_subset_range (I := I) hy)
    have htarget : I.symm (e.extend I x) ∈ e.target := by
      have hy' := hy
      rw [e.extend_target (I := I)] at hy'
      exact hy'.1
    have he_symm : MDifferentiableAt I I e.symm (I.symm (e.extend I x)) :=
      (contMDiffAt_symm_of_mem_maximalAtlas he htarget).mdifferentiableAt (by simp)
    simpa [OpenPartialHomeomorph.extend_coe_symm] using
      he_symm.comp_mdifferentiableWithinAt_of_eq
        (f := I.symm) (s := Set.range I) (x := e.extend I x) hI rfl
  have hchart_within :
      mfderiv I 𝓘(𝕜, E) (e.extend I) x =
        mfderivWithin I 𝓘(𝕜, E) (e.extend I) (e.extend I).source x := by
    rw [mfderivWithin_eq_mfderiv hsource_unique hchart]
  rw [hchart_within, ← mfderivWithin_comp_of_eq]
  · rw [← mfderivWithin_id hsource_unique]
    apply Filter.EventuallyEq.mfderivWithin_eq
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Function.comp_def, PartialEquiv.left_inv (e.extend I) hz, id_eq]
    · exact (e.extend I).left_inv hx_source
  · exact hinv
  · exact hchart.mdifferentiableWithinAt
  · intro z hz
    exact e.extend_target_subset_range (I := I) ((e.extend I).map_source hz)
  · exact hsource_unique
  · rfl

omit [IsManifold I ∞ M] in
/-- The derivative of an extended maximal-atlas chart is injective. -/
private lemma mfderiv_extend_injective_538
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) :
    Function.Injective (mfderiv I 𝓘(𝕜, E) (e.extend I) x) := by
  let L := mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (Set.range I) (e.extend I x)
  have hx_source : x ∈ (e.extend I).source := by
    simpa [e.extend_source (I := I)] using hx
  intro v w hvw
  have hleft := mfderivWithin_extend_symm_comp_mfderiv_extend_538 (I := I) he hx
  have hx_left : (e.extend I).symm (e.extend I x) = x :=
    (e.extend I).left_inv hx_source
  have h := congrArg L hvw
  have hv : L (mfderiv I 𝓘(𝕜, E) (e.extend I) x v) = v := by
    simpa [L, hx_left, ContinuousLinearMap.comp_apply] using!
      congrArg (fun A : TangentSpace I x →L[𝕜] TangentSpace I x ↦ A v) hleft
  have hw : L (mfderiv I 𝓘(𝕜, E) (e.extend I) x w) = w := by
    simpa [L, hx_left, ContinuousLinearMap.comp_apply] using!
      congrArg (fun A : TangentSpace I x →L[𝕜] TangentSpace I x ↦ A w) hleft
  exact hv.symm.trans (h.trans hw)

/-- Differentiating the immersion normal form identifies the inclusion derivative, in chart
coordinates, with the standard model inclusion. -/
private lemma subtypeVal_chartPushforward_eq_model_538
    (hImm : IsImmersion J I ∞ (Subtype.val : S → M))
    (p : S) (w : TangentSpace J p) :
    let hImmAt := hImm.isImmersionAt p
    let L : E' →L[𝕜] E :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
    (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) (p : M))
      (mfderiv J I (Subtype.val : S → M) p w) =
      L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w) := by
  let hImmAt := hImm.isImmersionAt p
  let L : E' →L[𝕜] E :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
  have hEqOn :
      Set.EqOn ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M))
        (L ∘ (hImmAt.domChart.extend J)) hImmAt.domChart.source := by
    intro y hy
    have hy_target :
        hImmAt.domChart.extend J y ∈ (hImmAt.domChart.extend J).target :=
      (hImmAt.domChart.extend J).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hy
    simpa [Function.comp, L, OpenPartialHomeomorph.extend_coe,
      hImmAt.domChart.left_inv hy, ContinuousLinearMap.comp_apply] using
      hImmAt.writtenInCharts hy_target
  have hEq :
      ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M)) =ᶠ[𝓝 p]
        L ∘ (hImmAt.domChart.extend J) :=
    hEqOn.eventuallyEq_of_mem
      (hImmAt.domChart.open_source.mem_nhds hImmAt.mem_domChart_source)
  have hsub : MDifferentiableAt J I (Subtype.val : S → M) p :=
    hImm.contMDiff.mdifferentiableAt (by simp)
  have hdom : MDifferentiableAt J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p :=
    (hImmAt.domChart.contMDiffAt_extend hImmAt.domChart_mem_maximalAtlas
      hImmAt.mem_domChart_source).mdifferentiableAt (by simp)
  have hcod : MDifferentiableAt I 𝓘(𝕜, E) (hImmAt.codChart.extend I) (p : M) :=
    (hImmAt.codChart.contMDiffAt_extend hImmAt.codChart_mem_maximalAtlas
      hImmAt.mem_codChart_source).mdifferentiableAt (by simp)
  have hL : MDifferentiableAt 𝓘(𝕜, E') 𝓘(𝕜, E) L
      (hImmAt.domChart.extend J p) := L.mdifferentiableAt
  have hderivEq :
      mfderiv J 𝓘(𝕜, E)
          ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M)) p =
        mfderiv J 𝓘(𝕜, E) (L ∘ (hImmAt.domChart.extend J)) p :=
    hEq.mfderiv_eq
  have hleft :
      (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) (p : M))
          (mfderiv J I (Subtype.val : S → M) p w) =
        mfderiv J 𝓘(𝕜, E)
          ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M)) p w := by
    symm
    exact mfderiv_comp_apply (x := p) hcod hsub w
  have hright :
      mfderiv J 𝓘(𝕜, E) (L ∘ (hImmAt.domChart.extend J)) p w =
        L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w) := by
    have hchain := mfderiv_comp_apply (x := p) (g := L)
      (f := hImmAt.domChart.extend J) hL hdom w
    rw [ContinuousLinearMap.mfderiv_eq L] at hchain
    exact hchain
  exact hleft.trans <| hderivEq ▸ hright

/-- The manifold derivative of the inclusion belonging to an immersion is injective.  Mathlib's
immersion API records the chart normal form but deliberately leaves this derivative fact as a
TODO, so it is proved locally here. -/
private lemma subtypeVal_mfderiv_injective_538
    (hImm : IsImmersion J I ∞ (Subtype.val : S → M)) (p : S) :
    Function.Injective (mfderiv J I (Subtype.val : S → M) p) := by
  let hImmAt := hImm.isImmersionAt p
  let L : E' →L[𝕜] E :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
  have hL_injective : Function.Injective L := by
    intro u v huv
    have hpair : (u, (0 : hImmAt.complement)) = (v, (0 : hImmAt.complement)) := by
      apply hImmAt.equiv.injective
      simpa [L, ContinuousLinearMap.comp_apply] using huv
    exact (Prod.mk.inj hpair).1
  intro w₁ w₂ hw
  have hw_chart :
      L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₁) =
        L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₂) := by
    have hw₁_model :
        L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₁) =
          (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) (p : M))
            (mfderiv J I (Subtype.val : S → M) p w₁) := by
      simpa [hImmAt, L] using
        (subtypeVal_chartPushforward_eq_model_538 (I := I) (J := J) hImm p w₁).symm
    have hw₂_model :
        (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) (p : M))
            (mfderiv J I (Subtype.val : S → M) p w₂) =
          L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₂) := by
      simpa [hImmAt, L] using
        subtypeVal_chartPushforward_eq_model_538 (I := I) (J := J) hImm p w₂
    exact hw₁_model.trans <| by simpa [hw] using hw₂_model
  have hsource_chart := hL_injective hw_chart
  exact mfderiv_extend_injective_538 (I := J)
    hImmAt.domChart_mem_maximalAtlas hImmAt.mem_domChart_source hsource_chart

-- Proof sketch: differentiate the identity `Φ ∘ Subtype.val = constant` along `S` to show that
-- the image of the inclusion derivative lies in the kernel, then use surjectivity of `dΦₚ` and
-- finite-dimensional rank-nullity to identify the two subspaces by dimension.
/-- Proposition 5.38: if `Φ` is a local defining map for the embedded submanifold `S` on `U`, then
the tangent space of `S` at `p`, viewed inside `TangentSpace I (p : M)` via the inclusion
`Subtype.val : S → M`, is the kernel of `dΦₚ`, provided the defining-map target has the
submanifold codimension. The dimension equation is explicit: the fiber and surjectivity
conditions in `IsLocalDefiningMapOn` alone are insufficient for arbitrary models with corners. -/
theorem tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn {U : Set M} {Φ : M → N}
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → M))
    (hΦ : IsLocalDefiningMapOn I K S U Φ)
    (hcodim : Module.finrank 𝕜 E' + Module.finrank 𝕜 F = Module.finrank 𝕜 E)
    (p : S) (hpU : (p : M) ∈ U) :
    T[J; p] = (mfderiv I K Φ (p : M)).ker := by
  let ι : S → M := Subtype.val
  let A := mfderiv J I ι p
  let B := mfderiv I K Φ (p : M)
  letI : FiniteDimensional 𝕜 (TangentSpace J p) := by
    change FiniteDimensional 𝕜 E'
    infer_instance
  letI : FiniteDimensional 𝕜 (TangentSpace I (p : M)) := by
    change FiniteDimensional 𝕜 E
    infer_instance
  letI : FiniteDimensional 𝕜 (TangentSpace K (Φ (p : M))) := by
    change FiniteDimensional 𝕜 F
    infer_instance
  have hι_mdiff : MDifferentiableAt J I ι p :=
    (hS.contMDiff.mdifferentiable (by simp)) p
  have hΦ_mdiff : MDifferentiableAt I K Φ (p : M) :=
    (hΦ.smoothOn (p : M) hpU).contMDiffAt (hΦ.isOpen_source.mem_nhds hpU)
      |>.mdifferentiableAt (by simp)
  have hconst_eventually :
      (Φ ∘ ι) =ᶠ[𝓝 p] (fun _ : S ↦ Φ (p : M)) := by
    have hpre : ι ⁻¹' U ∈ 𝓝 p :=
      hS.isEmbedding.continuous.continuousAt (hΦ.isOpen_source.mem_nhds hpU)
    filter_upwards [hpre] with q hq
    exact (hΦ.mem_iff_eq p.property hpU hq).mp q.property
  have hcomp : mfderiv J K (Φ ∘ ι) p = B.comp A := by
    simpa [A, B, ι] using mfderiv_comp p hΦ_mdiff hι_mdiff
  have hrange_le : A.range ≤ B.ker := by
    rintro v ⟨w, rfl⟩
    change B (A w) = 0
    change (B.comp A) w = 0
    rw [← hcomp, hconst_eventually.mfderiv_eq, mfderiv_const]
    rfl
  have hA_inj : Function.Injective A := by
    simpa [A, ι] using subtypeVal_mfderiv_injective_538 (I := I) (J := J) hS.isImmersion p
  have hB_surj : Function.Surjective B := by
    simpa [B] using hΦ.surjective_mfderiv hpU
  have hrangeA_finrank : Module.finrank 𝕜 A.range = Module.finrank 𝕜 E' := by
    have h := LinearMap.finrank_range_of_inj hA_inj
    exact h.trans (by rfl)
  have hrangeB : B.range = ⊤ := LinearMap.range_eq_top.mpr hB_surj
  have hrankNullity := B.toLinearMap.finrank_range_add_finrank_ker
  have hker_finrank : Module.finrank 𝕜 B.ker = Module.finrank 𝕜 E' := by
    have hsum : Module.finrank 𝕜 F + Module.finrank 𝕜 B.ker =
        Module.finrank 𝕜 E := by
      rw [hrangeB, finrank_top] at hrankNullity
      exact hrankNullity
    omega
  change A.range = B.ker
  exact Submodule.eq_of_le_of_finrank_eq hrange_le (hrangeA_finrank.trans hker_finrank.symm)

end SubmanifoldTangentSpace
