import MorganTianLib.Ch02.NeckVolume.CubicRescaling
import MorganTianLib.Ch02.NeckVolume.EpsilonMeasure

open Set MeasureTheory Riemannian Matrix Function
open scoped ContDiff Manifold Topology ENNReal Bundle BigOperators

noncomputable section
namespace MorganTianLib

local notation "E3" => EuclideanSpace ℝ (Fin (2 + 1))
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E3 H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
  [SigmaCompactSpace N] [T2Space N] [Nonempty N]

/-- **Math.** Actual neck volume compared to its round reference metric. -/
theorem epsilonNeck_volume_comparison
    (mu : Measure E3) [mu.IsAddHaarMeasure]
    {epsilon : ℝ} {g : RiemannianMetric I N} {x : N}
    (S : EpsilonNeckStructure epsilon g x)
    {s : Set (epsilonNeckDomain epsilon)} (hs : MeasurableSet s) :
    letI : Nonempty (epsilonNeckDomain epsilon) := ⟨S.phi.symm x⟩
    ENNReal.ofReal (S.scale ^ 3 * Real.sqrt ((1 - epsilon) ^ 3)) *
        riemannianMeasure (I := EpsilonNeckCylinderModel) S.referenceMetric mu s ≤
      riemannianMeasure (I := I) g mu (S.phi '' s) ∧
    riemannianMeasure (I := I) g mu (S.phi '' s) ≤
      ENNReal.ofReal (S.scale ^ 3 * Real.sqrt ((1 + epsilon) ^ 3)) *
        riemannianMeasure (I := EpsilonNeckCylinderModel) S.referenceMetric mu s := by
/- SWARM_PROOF_BEGIN -/
  letI : Nonempty (epsilonNeckDomain epsilon) := ⟨S.phi.symm x⟩
  obtain ⟨hscale, _, _⟩ := epsilonNeck_scale_pos_and_metric_normalization S
  have hcomp := riemannianMeasure_comparison_of_epsilonClose
    (I := EpsilonNeckCylinderModel) mu S.close hs
  have hrescale := epsilonNeck_volume_rescaling mu S hs
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  rw [hdim] at hcomp
  constructor
  · rw [hrescale]
    calc
      ENNReal.ofReal (S.scale ^ 3 * Real.sqrt ((1 - epsilon) ^ 3)) *
          riemannianMeasure (I := EpsilonNeckCylinderModel) S.referenceMetric mu s =
        ENNReal.ofReal (S.scale ^ 3) *
          (ENNReal.ofReal (Real.sqrt ((1 - epsilon) ^ 3)) *
            riemannianMeasure (I := EpsilonNeckCylinderModel)
              S.referenceMetric mu s) := by
            rw [ENNReal.ofReal_mul (pow_nonneg hscale.le 3)]
            ac_rfl
      _ ≤ ENNReal.ofReal (S.scale ^ 3) *
          riemannianMeasure (I := EpsilonNeckCylinderModel)
            S.normalizedPullbackMetric mu s :=
        mul_le_mul_left' hcomp.1 _
  · rw [hrescale]
    calc
      ENNReal.ofReal (S.scale ^ 3) *
          riemannianMeasure (I := EpsilonNeckCylinderModel)
            S.normalizedPullbackMetric mu s ≤
        ENNReal.ofReal (S.scale ^ 3) *
          (ENNReal.ofReal (Real.sqrt ((1 + epsilon) ^ 3)) *
            riemannianMeasure (I := EpsilonNeckCylinderModel)
              S.referenceMetric mu s) :=
        mul_le_mul_left' hcomp.2 _
      _ = ENNReal.ofReal (S.scale ^ 3 * Real.sqrt ((1 + epsilon) ^ 3)) *
          riemannianMeasure (I := EpsilonNeckCylinderModel) S.referenceMetric mu s := by
            rw [ENNReal.ofReal_mul (pow_nonneg hscale.le 3)]
            ac_rfl
/- SWARM_PROOF_END -/

end MorganTianLib
