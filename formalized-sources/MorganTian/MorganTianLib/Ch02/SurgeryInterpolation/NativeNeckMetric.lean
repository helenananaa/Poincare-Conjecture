import MorganTianLib.Ch02.SurgeryInterpolation.NeckMetric
import MorganTianLib.Ch02.SurgeryInterpolation.NativeCoordinate
import MorganTianLib.Ch02.NeckVolume.ActualVolumeComparison
import MorganTianLib.Ch01.MetricRescaling

open Set MeasureTheory Riemannian
open scoped ContDiff Manifold Topology ENNReal
noncomputable section
namespace MorganTianLib.SurgeryInterpolation
local notation "E3" => EuclideanSpace ℝ (Fin 3)
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E3 H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
  [SigmaCompactSpace N] [T2Space N] [Nonempty N]

/-- **Math.** A genuine smooth neck-side surgery metric, returned at the original scale.
It agrees with the old metric on the retained side and never increases volume.
The cap, the topology change and the curvature estimates are not constructed here. -/
theorem exists_native_neck_surgeryMetric
    (mu : Measure E3) [mu.IsAddHaarMeasure]
    {epsilon : ℝ} {g : RiemannianMetric I N} {x : N}
    (S : EpsilonNeckStructure epsilon g x)
    (amplitude q : ℝ) (ha : 0 ≤ amplitude) (hq : 0 < q) :
    letI : Nonempty (epsilonNeckDomain epsilon) := ⟨S.phi.symm x⟩
    ∃ gh : RiemannianMetric EpsilonNeckCylinderModel (epsilonNeckDomain epsilon),
      (∀ p v w, gh.metricInner p v w = S.scale ^ 2 *
        (Real.exp (-2 * neckProfile amplitude q (nativeAxis p)) *
          (neckCutoff (nativeAxis p) * S.normalizedPullbackMetric.metricInner p v w +
            (1 - neckCutoff (nativeAxis p)) * (1 - epsilon) *
              S.referenceMetric.metricInner p v w))) ∧
      (∀ p, nativeAxis p ≤ 0 → ∀ v w, gh.metricInner p v w =
        g.metricInner (S.phi p) (mfderiv EpsilonNeckCylinderModel I S.phi p v)
          (mfderiv EpsilonNeckCylinderModel I S.phi p w)) ∧
      (∀ p v, gh.metricInner p v v ≤
        g.metricInner (S.phi p) (mfderiv EpsilonNeckCylinderModel I S.phi p v)
          (mfderiv EpsilonNeckCylinderModel I S.phi p v)) ∧
      (∀ A : Set (epsilonNeckDomain epsilon), MeasurableSet A →
        riemannianMeasure (I := EpsilonNeckCylinderModel) gh mu A ≤
          riemannianMeasure (I := I) g mu (S.phi '' A)) := by
  letI : Nonempty (epsilonNeckDomain epsilon) := ⟨S.phi.symm x⟩
  have heta : 0 < 1 - epsilon := by
    have he := S.close
    have hehalf : epsilon < 1 / 2 := he.2.1
    linarith
  have hdom : ∀ p v, (1 - epsilon) * S.referenceMetric.metricInner p v v ≤
      S.normalizedPullbackMetric.metricInner p v v :=
    fun p v ↦ (epsilonClose_metricInner_comparison S.close p v).1
  obtain ⟨ghat, hformula, hleft, hright, hle⟩ := exists_neck_interpolationMetric
    S.normalizedPullbackMetric S.referenceMetric nativeAxis
    (nativeAxis_contMDiff epsilon) amplitude q (1 - epsilon) ha hq heta hdom
  obtain ⟨hh, _, hnorm⟩ := epsilonNeck_scale_pos_and_metric_normalization S
  let gh := rescaledMetric ghat (S.scale ^ 2) (sq_pos_of_pos hh)
  refine ⟨gh, ?_, ?_, ?_, ?_⟩
  · intro p v w
    rw [rescaledMetric_metricInner, hformula]
  · intro p hp v w
    rw [rescaledMetric_metricInner, hleft p hp v w]
    exact (hnorm p v w).symm
  · intro p v
    rw [rescaledMetric_metricInner, hnorm]
    exact mul_le_mul_of_nonneg_left (hle p v) (sq_nonneg _)
  · intro A hA
    have hm : riemannianMeasure (I := EpsilonNeckCylinderModel) ghat mu A ≤
        riemannianMeasure (I := EpsilonNeckCylinderModel) S.normalizedPullbackMetric mu A := by
      have hc := riemannianMeasure_global_chartDensity_comparison
        (I := EpsilonNeckCylinderModel) (mu := mu)
        (g₀ := S.normalizedPullbackMetric) (g₁ := ghat) hA
        (Cminus := 0) (Cplus := 1) (by norm_num) (by norm_num) (by
          intro alpha y hy
          have hd := chartVolumeDensity_comparison_of_metricInner
            (I := EpsilonNeckCylinderModel) (g0 := S.normalizedPullbackMetric)
            (g := ghat) (c0 := 0) (c1 := 1) (by norm_num) (by norm_num)
            alpha (chartPreimage_subset_target alpha A hy) (by
              intro v
              constructor
              · simpa using ghat.metricInner_self_nonneg _ v
              · simpa using hle ((extChartAt EpsilonNeckCylinderModel alpha).symm y) v)
          simpa using hd)
      simpa using hc.2
    have hsqrt : Real.sqrt ((S.scale ^ 2) ^ Module.finrank ℝ E3) = S.scale ^ 3 := by
      have hdim : Module.finrank ℝ E3 = 3 := by simp
      rw [hdim, show (S.scale ^ 2) ^ 3 = (S.scale ^ 3) ^ 2 by ring]
      exact Real.sqrt_sq (pow_nonneg hh.le 3)
    rw [epsilonNeck_volume_rescaling mu S hA]
    change riemannianMeasure (I := EpsilonNeckCylinderModel)
      (rescaledMetric ghat (S.scale ^ 2) (sq_pos_of_pos hh)) mu A ≤ _
    rw [rescaledMetric_riemannianMeasure, Measure.smul_apply, hsqrt]
    exact mul_le_mul_left' hm _

end MorganTianLib.SurgeryInterpolation
