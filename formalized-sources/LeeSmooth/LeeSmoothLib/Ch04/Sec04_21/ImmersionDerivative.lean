import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.SmoothEmbedding
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
namespace Manifold
section
universe u𝕜 uE uE' uH uH' uM uP
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H' P]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ P]
variable {f : P → M}
omit [IsManifold I ∞ M] in
/-- The derivative of an extended maximal-atlas chart has a left inverse, also for models with
corners.  This is the chart-level cancellation needed below; it does not use a boundaryless
model assumption. -/
private lemma mfderivWithin_extend_symm_comp_mfderiv_extend_sweep
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
private lemma mfderiv_extend_injective_sweep
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) :
    Function.Injective (mfderiv I 𝓘(𝕜, E) (e.extend I) x) := by
  let L := mfderivWithin 𝓘(𝕜, E) I (e.extend I).symm (Set.range I) (e.extend I x)
  have hx_source : x ∈ (e.extend I).source := by
    simpa [e.extend_source (I := I)] using hx
  intro v w hvw
  have hleft := mfderivWithin_extend_symm_comp_mfderiv_extend_sweep (I := I) he hx
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
private lemma subtypeVal_chartPushforward_eq_model_sweep
    (hImm : IsImmersion J I ∞ f)
    (p : P) (w : TangentSpace J p) :
    let hImmAt := hImm.isImmersionAt p
    let L : E' →L[𝕜] E :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
    (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) (f p))
      (mfderiv J I f p w) =
      L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w) := by
  let hImmAt := hImm.isImmersionAt p
  let L : E' →L[𝕜] E :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
  have hEqOn :
      Set.EqOn ((hImmAt.codChart.extend I) ∘ f)
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
      ((hImmAt.codChart.extend I) ∘ f) =ᶠ[𝓝 p]
        L ∘ (hImmAt.domChart.extend J) :=
    hEqOn.eventuallyEq_of_mem
      (hImmAt.domChart.open_source.mem_nhds hImmAt.mem_domChart_source)
  have hsub : MDifferentiableAt J I f p :=
    hImm.contMDiff.mdifferentiableAt (by simp)
  have hdom : MDifferentiableAt J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p :=
    (hImmAt.domChart.contMDiffAt_extend hImmAt.domChart_mem_maximalAtlas
      hImmAt.mem_domChart_source).mdifferentiableAt (by simp)
  have hcod : MDifferentiableAt I 𝓘(𝕜, E) (hImmAt.codChart.extend I) (f p) :=
    (hImmAt.codChart.contMDiffAt_extend hImmAt.codChart_mem_maximalAtlas
      hImmAt.mem_codChart_source).mdifferentiableAt (by simp)
  have hL : MDifferentiableAt 𝓘(𝕜, E') 𝓘(𝕜, E) L
      (hImmAt.domChart.extend J p) := L.mdifferentiableAt
  have hderivEq :
      mfderiv J 𝓘(𝕜, E)
          ((hImmAt.codChart.extend I) ∘ f) p =
        mfderiv J 𝓘(𝕜, E) (L ∘ (hImmAt.domChart.extend J)) p :=
    hEq.mfderiv_eq
  have hleft :
      (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) (f p))
          (mfderiv J I f p w) =
        mfderiv J 𝓘(𝕜, E)
          ((hImmAt.codChart.extend I) ∘ f) p w := by
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
theorem IsImmersion.mfderiv_injective
    (hImm : IsImmersion J I ∞ f) (p : P) :
    Function.Injective (mfderiv J I f p) := by
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
          (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) (f p))
            (mfderiv J I f p w₁) := by
      simpa [hImmAt, L] using
        (subtypeVal_chartPushforward_eq_model_sweep (I := I) (J := J) hImm p w₁).symm
    have hw₂_model :
        (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) (f p))
            (mfderiv J I f p w₂) =
          L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₂) := by
      simpa [hImmAt, L] using
        subtypeVal_chartPushforward_eq_model_sweep (I := I) (J := J) hImm p w₂
    exact hw₁_model.trans <| by simpa [hw] using hw₂_model
  have hsource_chart := hL_injective hw_chart
  exact mfderiv_extend_injective_sweep (I := J)
    hImmAt.domChart_mem_maximalAtlas hImmAt.mem_domChart_source hsource_chart


end
end Manifold
