import MorganTianLib.Ch02.NeckVolume.RoundDensityModel

open Set MeasureTheory Riemannian Bundle Function
open scoped ContDiff Manifold Topology ENNReal Bundle RealInnerProductSpace
noncomputable section
namespace MorganTianLib

set_option maxHeartbeats 800000 in
/-- **Math.** The actual transported-cylinder chart density is independent of
its axial coordinate and the finite neck length. -/
theorem roundCylinder_chartVolumeDensity_eq_coordinateDensity
    (alpha : EpsilonNeckSphere) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (g0 : RiemannianMetric EpsilonNeckCylinderModel (epsilonNeckDomain epsilon))
    (hround : IsRoundCylinderMetric epsilon g0)
    (u : EuclideanSpace ℝ (Fin 2)) (hu : u ∈ (extChartAt (𝓡 2) alpha).target)
    (t : EpsilonNeckAxis) (ht : -epsilon⁻¹ < t 0 ∧ t 0 < epsilon⁻¹) :
    let a : epsilonNeckDomain epsilon :=
      ⟨(alpha, 0), by constructor <;> simpa using inv_pos.mpr hepsilon⟩
    let z := epsilonNeckModelEquiv (u, t)
    z ∈ (extChartAt EpsilonNeckCylinderModel a).target ∧
      chartVolumeDensity (I := EpsilonNeckCylinderModel) g0 a z =
        roundCylinderCoordinateDensity alpha u := by
/- SWARM_PROOF_BEGIN -/
  let a : epsilonNeckDomain epsilon :=
    ⟨(alpha, 0), by constructor <;> simpa using inv_pos.mpr hepsilon⟩
  let z := epsilonNeckModelEquiv (u, t)
  change z ∈ (extChartAt EpsilonNeckCylinderModel a).target ∧
    chartVolumeDensity (I := EpsilonNeckCylinderModel) g0 a z =
      roundCylinderCoordinateDensity alpha u
  have htarget : (u, t) ∈
      (extChartAt EpsilonNeckProductModel a).target := by
    rw [extChartAt_target]
    simp only [mem_inter_iff, mem_preimage, ModelWithCorners.coe_transContinuousLinearEquiv_symm,
      Function.comp_apply]
    rw [TopologicalSpace.Opens.chartAt_eq]
    simp [OpenPartialHomeomorph.subtypeRestr_def]
    constructor
    · refine ⟨?_, mem_univ _⟩
      simpa [extChartAt_target] using hu
    · change -epsilon⁻¹ < t 0 ∧ t 0 < epsilon⁻¹
      exact ht
  constructor
  · simpa only [ModelWithCorners.extChartAt_transContinuousLinearEquiv_target,
      mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using (show
        epsilonNeckModelEquiv.symm z ∈
          (extChartAt EpsilonNeckProductModel a).target by simpa [z] using htarget)
  · let p : epsilonNeckDomain epsilon :=
      ⟨((extChartAt (𝓡 2) alpha).symm u, t), by
        change -epsilon⁻¹ < t 0 ∧ t 0 < epsilon⁻¹
        exact ht⟩
    have hp : (extChartAt EpsilonNeckCylinderModel a).symm z = p := by
      have hy : ((extChartAt (𝓡 2) alpha).symm u, t) ∈ epsilonNeckDomain epsilon := by
        change -epsilon⁻¹ < t 0 ∧ t 0 < epsilon⁻¹
        exact ht
      have hq : (chartAt (EuclideanSpace ℝ (Fin 2)) alpha).symm u =
          (extChartAt (𝓡 2) alpha).symm u := by
        rw [extChartAt_coe_symm]
        simp only [Function.comp_apply, modelWithCornersSelf_coe_symm, id_eq]
      have hprodq :
          ((chartAt (EuclideanSpace ℝ (Fin 2)) alpha).toPartialEquiv.prod
              (PartialEquiv.refl EpsilonNeckAxis)).symm
            ((PartialEquiv.refl
              (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))).symm (u, t)) =
            ((extChartAt (𝓡 2) alpha).symm u, t) := by
        rw [PartialEquiv.prod_symm]
        exact Prod.ext hq rfl
      apply Subtype.ext
      rw [ModelWithCorners.coe_extChartAt_transContinuousLinearEquiv_symm]
      simpa [z, a, p, hprodq, TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_def] using
        (epsilonNeckDomain epsilon).openPartialHomeomorphSubtypeCoe
          ⟨a⟩ |>.right_inv (by
            rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
            exact hy)
    have hgram :
        Riemannian.Tensor.chartGramMatrix (I := EpsilonNeckCylinderModel)
            g0 a p = roundCylinderCoordinateGram alpha u := by
      let A : EuclideanSpace ℝ (Fin 2) →L[ℝ]
          TangentSpace (𝓡 2) ((extChartAt (𝓡 2) alpha).symm u) :=
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2)
          (extChartAt (𝓡 2) alpha).symm u
      have hu' : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2)
          (extChartAt (𝓡 2) alpha).symm u := by
        rw [← mdifferentiableWithinAt_univ, ← (𝓡 2).range_eq_univ]
        exact mdifferentiableWithinAt_extChartAt_symm hu
      have hprod :
          mfderiv ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod
            (𝓘(ℝ, EuclideanSpace ℝ (Fin 1))))
              EpsilonNeckProductModel
              (fun y : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) =>
                ((extChartAt (𝓡 2) alpha).symm y.1, y.2)) (u, t) =
            A.prodMap (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) := by
        simpa only [Prod.map_def, mfderiv_id, id_eq] using!
          (mfderiv_prodMap
            (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
            (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)))
            (J := 𝓡 2) (J' := 𝓡 1)
            (f := (extChartAt (𝓡 2) alpha).symm) (g := id)
            hu' mdifferentiableAt_id)
      have hq_source : (extChartAt (𝓡 2) alpha).symm u ∈
          (chartAt (EuclideanSpace ℝ (Fin 2)) alpha).source := by
        rw [← extChartAt_source (I := 𝓡 2)]
        exact (extChartAt (𝓡 2) alpha).map_target hu
      have hp_source : p ∈
          (chartAt (ModelProd (EuclideanSpace ℝ (Fin 2))
            (EuclideanSpace ℝ (Fin 1))) a).source := by
        rw [TopologicalSpace.Opens.chartAt_eq,
          OpenPartialHomeomorph.subtypeRestr_source]
        change ((extChartAt (𝓡 2) alpha).symm u, t) ∈
          (chartAt (ModelProd (EuclideanSpace ℝ (Fin 2))
            (EuclideanSpace ℝ (Fin 1))) (alpha, 0)).source
        rw [← extChartAt_source (I := EpsilonNeckProductModel), extChartAt_prod,
          PartialEquiv.prod_source]
        refine ⟨?_, ?_⟩
        · exact (extChartAt (𝓡 2) alpha).map_target hu
        · rw [extChartAt_source (I := 𝓡 1)]
          simp
      have hp_source' : p ∈
          (extChartAt EpsilonNeckProductModel a).source := by
        rw [extChartAt_source (I := EpsilonNeckProductModel)]
        exact hp_source
      have hmodel_conj :
          tangentCoordChange EpsilonNeckCylinderModel a p p =
            epsilonNeckModelEquiv.toContinuousLinearMap ∘L
              (tangentCoordChange EpsilonNeckProductModel a p p) ∘L
                epsilonNeckModelEquiv.symm.toContinuousLinearMap := by
        let f := (extChartAt EpsilonNeckProductModel p) ∘
          (extChartAt EpsilonNeckProductModel a).symm
        let x := extChartAt EpsilonNeckProductModel a p
        have hd : HasFDerivAt f
          (tangentCoordChange EpsilonNeckProductModel a p p) x := by
          have h := hasFDerivWithinAt_tangentCoordChange
            (I := EpsilonNeckProductModel) (x := a) (y := p) (z := p)
              ⟨hp_source', mem_extChartAt_source _⟩
          rw [EpsilonNeckProductModel.range_eq_univ,
            hasFDerivWithinAt_univ] at h
          exact h
        have hd' : HasFDerivAt f
            (tangentCoordChange EpsilonNeckProductModel a p p)
            (epsilonNeckModelEquiv.symm
              (epsilonNeckModelEquiv x)) := by
          simpa only [epsilonNeckModelEquiv.symm_apply_apply] using hd
        have hc := (epsilonNeckModelEquiv.toContinuousLinearMap.hasFDerivAt).comp
          (epsilonNeckModelEquiv x)
            (hd'.comp (epsilonNeckModelEquiv x)
              epsilonNeckModelEquiv.symm.toContinuousLinearMap.hasFDerivAt)
        rw [tangentCoordChange_def, EpsilonNeckCylinderModel.range_eq_univ,
          fderivWithin_univ]
        change fderiv ℝ ((epsilonNeckModelEquiv ∘
          (extChartAt EpsilonNeckProductModel p)) ∘
            ((extChartAt EpsilonNeckProductModel a).symm ∘
              epsilonNeckModelEquiv.symm))
          (epsilonNeckModelEquiv x) = _
        simpa only [f, Function.comp_assoc] using! hc.fderiv
      have hprod_transition :
          tangentCoordChange EpsilonNeckProductModel
              (alpha, (0 : EpsilonNeckAxis))
              ((extChartAt (𝓡 2) alpha).symm u, t)
              ((extChartAt (𝓡 2) alpha).symm u, t) =
            (tangentCoordChange (𝓡 2) alpha
                ((extChartAt (𝓡 2) alpha).symm u)
                ((extChartAt (𝓡 2) alpha).symm u)).prodMap
              (tangentCoordChange (𝓡 1) (0 : EpsilonNeckAxis) t t) := by
        have h1 := hasFDerivWithinAt_tangentCoordChange
          (I := 𝓡 2) ⟨(extChartAt (𝓡 2) alpha).map_target hu,
            mem_extChartAt_source _⟩
        have h2 := hasFDerivWithinAt_tangentCoordChange
          (I := 𝓡 1) (x := (0 : EpsilonNeckAxis)) (y := t) (z := t)
          ⟨by
            rw [extChartAt_source (I := 𝓡 1), chartAt_self_eq]
            change t ∈ (Homeomorph.refl EpsilonNeckAxis).toOpenPartialHomeomorph.source
            exact mem_univ _,
            by rw [extChartAt_source (I := 𝓡 1)]; exact mem_chart_source _ _⟩
        rw [(𝓡 2).range_eq_univ,
          hasFDerivWithinAt_univ] at h1
        rw [(𝓡 1).range_eq_univ,
          hasFDerivWithinAt_univ] at h2
        rw [tangentCoordChange_def, EpsilonNeckProductModel.range_eq_univ,
          fderivWithin_univ]
        exact (HasFDerivAt.prodMap
          (extChartAt EpsilonNeckProductModel
            (alpha, (0 : EpsilonNeckAxis))
            ((extChartAt (𝓡 2) alpha).symm u, t)) h1 h2).fderiv
      have hopenprod :
          tangentCoordChange EpsilonNeckProductModel a p p =
            tangentCoordChange EpsilonNeckProductModel
              (alpha, (0 : EpsilonNeckAxis))
              ((extChartAt (𝓡 2) alpha).symm u, t)
              ((extChartAt (𝓡 2) alpha).symm u, t) := by
        have hlocal :
            ((extChartAt EpsilonNeckProductModel p) ∘
                (extChartAt EpsilonNeckProductModel a).symm) =ᶠ[
              𝓝 (extChartAt EpsilonNeckProductModel a p)]
              ((extChartAt EpsilonNeckProductModel p.1) ∘
                (extChartAt EpsilonNeckProductModel a.1).symm) := by
          filter_upwards [(isOpen_extChartAt_target a).mem_nhds
            ((extChartAt EpsilonNeckProductModel a).map_source hp_source')] with z hz
          let q : epsilonNeckDomain epsilon :=
            (extChartAt EpsilonNeckProductModel a).symm z
          have hq : q.1 ∈
              (extChartAt EpsilonNeckProductModel a.1).source := by
            simpa only [extChartAt_source, TopologicalSpace.Opens.chartAt_eq,
              OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage]
              using (extChartAt EpsilonNeckProductModel a).map_target hz
          have hcoord : extChartAt EpsilonNeckProductModel a.1 q.1 = z :=
            (extChartAt EpsilonNeckProductModel a).right_inv hz
          have hinv : (extChartAt EpsilonNeckProductModel a.1).symm z = q.1 := by
            rw [← hcoord]
            exact (extChartAt EpsilonNeckProductModel a.1).left_inv hq
          change extChartAt EpsilonNeckProductModel p.1 q.1 =
            extChartAt EpsilonNeckProductModel p.1
              ((extChartAt EpsilonNeckProductModel a.1).symm z)
          rw [hinv]
        simp only [tangentCoordChange_def, EpsilonNeckProductModel.range_eq_univ,
          fderivWithin_univ]
        exact hlocal.fderiv_eq
      have haxis : tangentCoordChange (𝓡 1) (0 : EpsilonNeckAxis) t t =
          (ContinuousLinearMap.id ℝ EpsilonNeckAxis) := by
        exact TangentBundle.coordChange_model_space _ _ _
      have hraw (v : EuclideanSpace ℝ (Fin 3)) :
          epsilonNeckModelEquiv.symm ((tangentCoordChange EpsilonNeckCylinderModel a p p) v) =
            ((tangentCoordChange (𝓡 2) alpha ((extChartAt (𝓡 2) alpha).symm u)
              ((extChartAt (𝓡 2) alpha).symm u)) (epsilonNeckModelEquiv.symm v).1,
              (epsilonNeckModelEquiv.symm v).2) := by
        rw [hmodel_conj, hopenprod, hprod_transition, haxis]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.symm_apply_apply]
        rfl
      have hcore (v : EuclideanSpace ℝ (Fin 3)) :
          (trivializationAt (EuclideanSpace ℝ (Fin 3))
              (TangentSpace EpsilonNeckCylinderModel) a).symm p v =
            (tangentCoordChange EpsilonNeckCylinderModel a p p) v := by
        have hb : p ∈ (trivializationAt (EuclideanSpace ℝ (Fin 3))
            (TangentSpace EpsilonNeckCylinderModel) a).baseSet := by
          rw [trivializationAt_baseSet_eq_chartAt_source]
          exact hp_source
        have h := congrArg (fun L => L v)
          (TangentBundle.symmL_trivializationAt_eq_core (I := EpsilonNeckCylinderModel) hp_source)
        simpa only [Bundle.Trivialization.symmL_apply _ hb] using! h
      have hsphere (v : EuclideanSpace ℝ (Fin 2)) :
          (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) alpha).symm
              ((extChartAt (𝓡 2) alpha).symm u) v =
            (tangentCoordChange (𝓡 2) alpha ((extChartAt (𝓡 2) alpha).symm u)
              ((extChartAt (𝓡 2) alpha).symm u)) v := by
        have hb : (extChartAt (𝓡 2) alpha).symm u ∈
            (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) alpha).baseSet := by
          rw [trivializationAt_baseSet_eq_chartAt_source]
          exact hq_source
        have h := congrArg (fun L => L v)
          (TangentBundle.symmL_trivializationAt_eq_core (I := 𝓡 2) hq_source)
        simpa only [Bundle.Trivialization.symmL_apply _ hb] using! h
      have hframe (v : EuclideanSpace ℝ (Fin 3)) :
          epsilonNeckModelEquiv.symm
            ((trivializationAt (EuclideanSpace ℝ (Fin 3))
                (TangentSpace EpsilonNeckCylinderModel) a).symm p v) =
            ((trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) alpha).symm
              ((extChartAt (𝓡 2) alpha).symm u) (epsilonNeckModelEquiv.symm v).1,
              (epsilonNeckModelEquiv.symm v).2) := by
        rw [hcore, hraw, hsphere]
      ext i j
      change g0.metricInner p
        ((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace EpsilonNeckCylinderModel) a).symm p
          (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3)) i))
        ((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace EpsilonNeckCylinderModel) a).symm p
          (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3)) j)) = _
      rw [hround.2]
      change roundSphereMetric.metricInner p.1.1
        (epsilonNeckModelEquiv.symm _).1 (epsilonNeckModelEquiv.symm _).1 +
        inner ℝ (epsilonNeckModelEquiv.symm _).2 (epsilonNeckModelEquiv.symm _).2 = _
      rw [hframe, hframe]
      rfl
    rw [chartVolumeDensity, hp, hgram, roundCylinderCoordinateDensity]
/- SWARM_PROOF_END -/

end MorganTianLib
