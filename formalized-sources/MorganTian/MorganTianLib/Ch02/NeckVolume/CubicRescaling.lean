import MorganTianLib.Ch02.NeckVolume.ScaleNormalization
import MorganTianLib.Ch02.NeckVolume.PullbackMeasure
import MorganTianLib.Ch01.MetricRescaling

open Set MeasureTheory Riemannian Matrix Function
open scoped ContDiff Manifold Topology ENNReal Bundle BigOperators

noncomputable section
namespace MorganTianLib

local notation "E3" => EuclideanSpace ℝ (Fin (2 + 1))
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E3 H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
  [SigmaCompactSpace N] [T2Space N] [Nonempty N]

/-- **Math.** Actual neck volume is h-cubed times its normalized pullback volume. -/
theorem epsilonNeck_volume_rescaling
    (mu : Measure E3) [mu.IsAddHaarMeasure]
    {epsilon : ℝ} {g : RiemannianMetric I N} {x : N}
    (S : EpsilonNeckStructure epsilon g x)
    {s : Set (epsilonNeckDomain epsilon)} (hs : MeasurableSet s) :
    letI : Nonempty (epsilonNeckDomain epsilon) := ⟨S.phi.symm x⟩
    riemannianMeasure (I := I) g mu (S.phi '' s) =
      ENNReal.ofReal (S.scale ^ 3) *
        riemannianMeasure (I := EpsilonNeckCylinderModel) S.normalizedPullbackMetric mu s := by
/- SWARM_PROOF_BEGIN -/
  letI : Nonempty (epsilonNeckDomain epsilon) := ⟨S.phi.symm x⟩
  obtain ⟨hscale, _, hmetric⟩ :=
    epsilonNeck_scale_pos_and_metric_normalization S
  have hc : 0 < S.scale ^ 2 := sq_pos_of_pos hscale
  have hpull : ∀ (p : epsilonNeckDomain epsilon)
      (v w : TangentSpace EpsilonNeckCylinderModel p),
      (rescaledMetric S.normalizedPullbackMetric (S.scale ^ 2) hc).metricInner
          p v w = g.metricInner (S.phi p)
            (mfderiv EpsilonNeckCylinderModel I S.phi p v)
            (mfderiv EpsilonNeckCylinderModel I S.phi p w) := by
    intro p v w
    rw [rescaledMetric_metricInner]
    exact (hmetric p v w).symm
  have himage := riemannianMeasure_image_of_pullback_metric
    (mu := mu) (rescaledMetric S.normalizedPullbackMetric (S.scale ^ 2) hc)
    g
    S.phi hpull hs
  have hrescale := rescaledMetric_riemannianMeasure
    (I := EpsilonNeckCylinderModel) (M := epsilonNeckDomain epsilon)
    mu S.normalizedPullbackMetric (S.scale ^ 2) hc
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  have hsqrt : Real.sqrt ((S.scale ^ 2) ^ 3) = S.scale ^ 3 := by
    rw [show (S.scale ^ 2) ^ 3 = (S.scale ^ 3) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (pow_pos hscale 3)]
  calc
    riemannianMeasure (I := I) g mu (S.phi '' s) =
        riemannianMeasure (I := EpsilonNeckCylinderModel)
          (rescaledMetric S.normalizedPullbackMetric (S.scale ^ 2) hc) mu s := himage
    _ = (ENNReal.ofReal (Real.sqrt ((S.scale ^ 2) ^ Module.finrank ℝ E3)) •
        riemannianMeasure (I := EpsilonNeckCylinderModel)
          S.normalizedPullbackMetric mu) s := by rw [hrescale]
    _ = ENNReal.ofReal (S.scale ^ 3) *
        riemannianMeasure (I := EpsilonNeckCylinderModel)
        S.normalizedPullbackMetric mu s := by
      rw [hdim, hsqrt, MeasureTheory.Measure.smul_apply]
      rfl
/- SWARM_PROOF_END -/

end MorganTianLib
