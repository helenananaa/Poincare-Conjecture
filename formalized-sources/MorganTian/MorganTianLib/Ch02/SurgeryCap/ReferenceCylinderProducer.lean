import MorganTianLib.Ch02.SurgeryCap.SphereIntrinsicCurvature
import MorganTianLib.Ch02.NeckVolume.CylinderModelFacts
import DoCarmoLib.Riemannian.Manifold.PullbackMetric
open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
/-- **Math.** A genuine reference metric satisfying the existing round-cylinder
contract; neither its curvature witness nor the metric itself is assumed. -/
theorem exists_reference_round_cylinder_metric (epsilon : ℝ) :
    ∃ g0 : RiemannianMetric EpsilonNeckCylinderModel (epsilonNeckDomain epsilon),
      IsRoundCylinderMetric epsilon g0 := by
/- SWARM_PROOF_BEGIN -/
  have hrestrict : ∀ p : epsilonNeckDomain epsilon,
      mfderiv EpsilonNeckProductModel EpsilonNeckProductModel
        (Subtype.val : epsilonNeckDomain epsilon → EpsilonNeckCylinder) p =
        ContinuousLinearMap.id ℝ (TangentSpace EpsilonNeckProductModel p) := by
    intro p
    have hc : MDifferentiableAt EpsilonNeckProductModel 𝓘(ℝ,
        EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))
        (extChartAt EpsilonNeckProductModel p.1) p.1 := by
      exact mdifferentiableAt_extChartAt (mem_chart_source _ p.1)
    have hv : MDifferentiableAt EpsilonNeckProductModel EpsilonNeckProductModel
        (Subtype.val : epsilonNeckDomain epsilon → EpsilonNeckCylinder) p :=
      (contMDiff_subtype_val (I := EpsilonNeckProductModel) (n := ∞)).mdifferentiableAt
        (by simp)
    have hcomp := mfderiv_comp p hc hv
    have hfun : (extChartAt EpsilonNeckProductModel p.1) ∘
        (Subtype.val : epsilonNeckDomain epsilon → EpsilonNeckCylinder) =
        (extChartAt EpsilonNeckProductModel p) := by
      rfl
    rw [hfun] at hcomp
    rw [mfderiv_extChartAt_self, mfderiv_extChartAt_self] at hcomp
    ext z
    have hz := congrArg (fun L => L z) hcomp
    change (ContinuousLinearMap.id ℝ (TangentSpace EpsilonNeckProductModel p)) z =
        (ContinuousLinearMap.id ℝ (TangentSpace EpsilonNeckProductModel p.1) ∘SL
          mfderiv EpsilonNeckProductModel EpsilonNeckProductModel
            (Subtype.val : epsilonNeckDomain epsilon → EpsilonNeckCylinder) p) z at hz
    change (mfderiv EpsilonNeckProductModel EpsilonNeckProductModel
        (Subtype.val : epsilonNeckDomain epsilon → EpsilonNeckCylinder) p) z = z
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hz.symm

  let productMetric : RiemannianMetric EpsilonNeckProductModel EpsilonNeckCylinder :=
    DCProductMetric roundSphereMetric (DCEuclideanMetric (F := EpsilonNeckAxis))
  have hsub : ∀ p : epsilonNeckDomain epsilon,
      Function.Injective (mfderiv EpsilonNeckProductModel EpsilonNeckProductModel
        (Subtype.val : epsilonNeckDomain epsilon → EpsilonNeckCylinder) p) := by
    intro p
    rw [hrestrict p]
    intro v w h
    exact h
  let nativeMetric : RiemannianMetric EpsilonNeckProductModel
      (epsilonNeckDomain epsilon) :=
    DCInducedMetric productMetric (Subtype.val : epsilonNeckDomain epsilon → EpsilonNeckCylinder)
      ⟨contMDiff_subtype_val, hsub⟩

  let changeModel : Diffeomorph EpsilonNeckProductModel EpsilonNeckCylinderModel
      (epsilonNeckDomain epsilon) (epsilonNeckDomain epsilon) ∞ :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv
      EpsilonNeckProductModel (epsilonNeckDomain epsilon) epsilonNeckModelEquiv
  have hmodel : ∀ p : epsilonNeckDomain epsilon,
      mfderiv EpsilonNeckCylinderModel EpsilonNeckProductModel changeModel.symm p =
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1) :
          EuclideanSpace ℝ (Fin (2 + 1)) →L[ℝ]
            EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) := by
    intro p
    let e := epsilonNeckModelEquiv
    let I := EpsilonNeckProductModel
    let J := I.transContinuousLinearEquiv e
    have hdiff : MDifferentiableAt J I (changeModel.symm) p :=
      changeModel.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hfun : (changeModel.symm : epsilonNeckDomain epsilon → epsilonNeckDomain epsilon) = id := by
      rfl
    have hfd : HasFDerivWithinAt
        (writtenInExtChartAt J I p (changeModel.symm))
        (e.symm : EuclideanSpace ℝ (Fin (2 + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))
        (Set.range J) ((extChartAt J p) p) := by
      apply (e.symm.hasFDerivAt.hasFDerivWithinAt).congr_of_eventuallyEq
      · have ht : Filter.Tendsto (e.symm : EuclideanSpace ℝ (Fin (2 + 1)) →
            EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))
            (𝓝[Set.range J] (e ((extChartAt I p) p)))
            (𝓝[Set.range I] ((extChartAt I p) p)) := by
          rw [tendsto_nhdsWithin_iff]
          have hecont : ContinuousWithinAt
              (e.symm : EuclideanSpace ℝ (Fin (2 + 1)) →
                EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))
              (Set.range J) (e ((extChartAt I p) p)) :=
            e.symm.continuous.continuousAt.continuousWithinAt
          refine ⟨by simpa using hecont.tendsto, ?_⟩
          filter_upwards [self_mem_nhdsWithin] with y hy
          rw [ModelWithCorners.transContinuousLinearEquiv_range] at hy
          rcases hy with ⟨z, hz, rfl⟩
          rcases hz with ⟨u, hu⟩
          refine ⟨u, ?_⟩
          simpa [hu]
        have hEq0 : ∀ᶠ z in 𝓝[Set.range I] ((extChartAt I p) p),
            (extChartAt I p) ((extChartAt I p).symm z) = z := by
          apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I := I) p)
          intro z hz
          exact (extChartAt I p).right_inv hz
        have hEq1 := ht.eventually hEq0
        change ∀ᶠ x in 𝓝[Set.range J] (e ((extChartAt I p) p)),
          (writtenInExtChartAt J I p (changeModel.symm)) x = e.symm x
        filter_upwards [hEq1] with x hx
        simpa [writtenInExtChartAt, Function.comp_apply, Function.comp_def,
          hfun, changeModel, J] using hx
      · have hpoint :
            (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞)
              EpsilonNeckProductModel (epsilonNeckDomain epsilon)
                epsilonNeckModelEquiv).symm p = p := by
          rfl
        have hpoint' :
            (changeModel.symm : epsilonNeckDomain epsilon → epsilonNeckDomain epsilon) p = p := by
          rfl
        change (extChartAt I (changeModel.symm p))
            (changeModel.symm ((extChartAt J p).symm ((extChartAt J p) p))) =
          e.symm ((extChartAt J p) p)
        rw [hpoint']
        have hchart : (extChartAt J p).symm ((extChartAt J p) p) = p :=
          (extChartAt J p).left_inv (mem_extChartAt_source p)
        rw [hchart, hpoint']
        simp [I, J]
    rw [mfderiv, if_pos hdiff]
    exact hfd.fderivWithin (ModelWithCorners.uniqueDiffWithinAt_image J)

  have hmodel_inj : ∀ p : epsilonNeckDomain epsilon,
      Function.Injective (mfderiv EpsilonNeckCylinderModel EpsilonNeckProductModel
        changeModel.symm p) := by
    intro p
    rw [hmodel p]
    exact EuclideanSpace.finAddEquivProd.injective
  let g0 : RiemannianMetric EpsilonNeckCylinderModel
      (epsilonNeckDomain epsilon) :=
    DCInducedMetric nativeMetric (changeModel.symm : epsilonNeckDomain epsilon → epsilonNeckDomain epsilon)
      ⟨changeModel.symm.contMDiff, hmodel_inj⟩
  refine ⟨g0, ?_, ?_⟩
  · exact roundSphereMetric_isConstantCurvature_of_unitRoundSphereMetric
      unitRoundSphereMetric_intrinsic_curvature_one
  · intro p v w
    change nativeMetric.metricInner (changeModel.symm p)
      (mfderiv EpsilonNeckCylinderModel EpsilonNeckProductModel
        changeModel.symm p v)
      (mfderiv EpsilonNeckCylinderModel EpsilonNeckProductModel
        changeModel.symm p w) = _
    rw [hmodel p]
    change nativeMetric.metricInner p
      (EuclideanSpace.finAddEquivProd v)
      (EuclideanSpace.finAddEquivProd w) = _
    change productMetric.metricInner p.1
      (mfderiv EpsilonNeckProductModel EpsilonNeckProductModel
        (Subtype.val : epsilonNeckDomain epsilon → EpsilonNeckCylinder) p
        (EuclideanSpace.finAddEquivProd v))
      (mfderiv EpsilonNeckProductModel EpsilonNeckProductModel
        (Subtype.val : epsilonNeckDomain epsilon → EpsilonNeckCylinder) p
        (EuclideanSpace.finAddEquivProd w)) = _
    rw [hrestrict p]
    change productMetric.metricInner p.1
      (EuclideanSpace.finAddEquivProd v)
      (EuclideanSpace.finAddEquivProd w) = _
    simp [productMetric, DCProductMetric, DCProductForm,
      DCInducedForm_apply, mfderiv_fst, mfderiv_snd]
    change roundSphereMetric.metricInner p.1.1
        (EuclideanSpace.finAddEquivProd v).1
        (EuclideanSpace.finAddEquivProd w).1 +
      inner ℝ (EuclideanSpace.finAddEquivProd v).2
        (EuclideanSpace.finAddEquivProd w).2 = _
    rfl
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
