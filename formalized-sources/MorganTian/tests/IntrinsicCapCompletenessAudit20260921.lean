import MorganTianLib.Ch02.SurgeryCap.GeodesicCompleteness
import Lean
set_option backward.isDefEq.respectTransparency false
open Riemannian Bundle Manifold
open scoped ContDiff Manifold
noncomputable section
local notation "E3" => EuclideanSpace ℝ (Fin 3)
open MorganTianLib.SurgeryCap

-- These typed consumers prevent silently auditing the pre-existing Euclidean structure.
example (P : RoundCapProfile) :
    letI : RiemannianBundle (fun x : E3 => TangentSpace (𝓡 3) x) :=
      ⟨P.globalMetric.toRiemannianMetric⟩
    let m : MetricSpace E3 := MetricSpace.ofRiemannianMetric (𝓡 3) E3
    @CompleteSpace E3 m.toUniformSpace := by
  exact (globalCap_intrinsic_proper_complete P).2

example (P : RoundCapProfile) :
    letI : RiemannianBundle (fun x : E3 => TangentSpace (𝓡 3) x) :=
      ⟨P.globalMetric.toRiemannianMetric⟩
    let m : MetricSpace E3 := MetricSpace.ofRiemannianMetric (𝓡 3) E3
    @ProperSpace E3 m.toPseudoMetricSpace := by
  exact (globalCap_intrinsic_proper_complete P).1

example : Riemannian.Geodesic.IsGeodesicallyComplete standardRoundCapProfile.globalMetric :=
  standardRoundCapProfile.globalMetric_geodesicallyComplete

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``globalCap_riemannianEDist_zero,
    ``globalCap_intrinsic_proper_complete,
    ``RoundCapProfile.globalMetric_geodesicallyComplete]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in targets do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let a ← Lean.collectAxioms n
    let unexpected := a.filter (fun x => !allowed.contains x)
    unless unexpected.isEmpty do throwError "Nonstandard axioms: {n}: {unexpected}"
    logInfo m!"PASS {n}: {a}"
  logInfo m!"EXPLICIT_INTRINSIC_COMPLETENESS_GUARD_PASS {targets.size}"
