import MorganTianLib.Ch02.SurgeryCap.Completeness
import DoCarmoLib.Riemannian.Geodesic.HopfRinow

open Riemannian Bundle Manifold
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** The constructed cap admits complete geodesics through every point
and tangent vector, for its actual global metric. -/
theorem RoundCapProfile.globalMetric_geodesicallyComplete (P : RoundCapProfile) :
    Riemannian.Geodesic.IsGeodesicallyComplete P.globalMetric := by
  letI : RiemannianBundle (fun x : E3 => TangentSpace (𝓡 3) x) :=
    ⟨P.globalMetric.toRiemannianMetric⟩
  let intrinsicMetric : MetricSpace E3 := MetricSpace.ofRiemannianMetric (𝓡 3) E3
  letI : MetricSpace E3 := intrinsicMetric
  letI : PseudoEMetricSpace E3 := intrinsicMetric.toEMetricSpace.toPseudoEMetricSpace
  letI : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  have hcomplete := globalCap_intrinsic_proper_complete P
  letI : @CompleteSpace E3 intrinsicMetric.toUniformSpace := hcomplete.2
  have hdist : P.globalMetric.IsRiemannianDist := by
    change IsRiemannianManifold (𝓡 3) E3
    constructor
    intro x y
    rfl
  exact Riemannian.Geodesic.isGeodesicallyComplete_of_complete P.globalMetric hdist

end MorganTianLib.SurgeryCap
