import MorganTianLib.Ch02.SurgeryCap.RadialDistance
import DoCarmoLib.Riemannian.Metric.RiemannianDistance

open Set Riemannian Bundle Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** The actual Riemannian distance of the smooth global cap is
proper and complete; this does not reuse Euclidean metric completeness. -/
theorem globalCap_intrinsic_proper_complete (P : RoundCapProfile) :
    letI : RiemannianBundle (fun x : E3 => TangentSpace (𝓡 3) x) :=
      ⟨P.globalMetric.toRiemannianMetric⟩
    letI : MetricSpace E3 := MetricSpace.ofRiemannianMetric (𝓡 3) E3
    ProperSpace E3 ∧ CompleteSpace E3 := by
/- SWARM_PROOF_BEGIN -/
  letI : RiemannianBundle (fun x : E3 => TangentSpace (𝓡 3) x) :=
    ⟨P.globalMetric.toRiemannianMetric⟩
  have euclideanClosedBallCompact (r : ℝ) :
      IsCompact {x : E3 | ‖x‖ ≤ r} := by
    simpa [Metric.closedBall, dist_zero_right] using
      (isCompact_closedBall (0 : E3) r)
  let intrinsicMetric : MetricSpace E3 := MetricSpace.ofRiemannianMetric (𝓡 3) E3
  letI : MetricSpace E3 := intrinsicMetric
  let intrinsicPseudoMetric : PseudoMetricSpace E3 := intrinsicMetric.toPseudoMetricSpace
  letI : PseudoMetricSpace E3 := intrinsicPseudoMetric
  letI : Dist E3 := intrinsicPseudoMetric.toDist
  have hdist0 (x : E3) :
      @dist E3 intrinsicMetric.toPseudoMetricSpace.toDist (0 : E3) x = ‖x‖ := by
    change ENNReal.toReal (Manifold.riemannianEDist (𝓡 3) (0 : E3) x) = ‖x‖
    rw [globalCap_riemannianEDist_zero P x]
    exact ENNReal.toReal_ofReal (norm_nonneg x)
  have intrinsicClosedBallCompact (r : ℝ) :
      IsCompact (Metric.closedBall (0 : E3) r) := by
    rw [show Metric.closedBall (0 : E3) r = {x : E3 | ‖x‖ ≤ r} by
      ext x
      simp only [Metric.mem_closedBall]
      rw [dist_comm, hdist0]
      rfl]
    exact euclideanClosedBallCompact r
  letI : ProperSpace E3 :=
    { isCompact_closedBall := by
        intro c r
        refine (intrinsicClosedBallCompact (dist (0 : E3) c + r)).of_isClosed_subset
          Metric.isClosed_closedBall ?_
        intro x hx
        rw [Metric.mem_closedBall] at hx ⊢
        have hxc : dist c x ≤ r := by simpa [dist_comm] using hx
        calc
          dist x 0 = dist 0 x := dist_comm _ _
          _ ≤ dist 0 c + dist c x := dist_triangle _ _ _
          _ ≤ dist 0 c + r := add_le_add_right hxc _ }
  exact ⟨inferInstance, inferInstance⟩
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
