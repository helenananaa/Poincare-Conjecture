import MorganTianLib.Ch02.SurgeryCap.PuncturedCap
import MorganTianLib.Ch02.SurgeryCap.WarpedConnection
import Lean

open MorganTianLib MorganTianLib.SurgeryCap
open scoped Manifold ContDiff

-- This tests an actual constructed profile and a nonzero radial tangent vector.
example (x : EpsilonNeckSphere) (r : ↥positiveReal) :
    standardRoundCapProfile.puncturedMetric.metricInner (x, r) (0, 1) (0, 1) = 1 :=
  standardRoundCapProfile.radial_unit x r

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``exists_round_tip_cylindrical_warping,
    ``nonempty_roundCapProfile,
    ``standardRoundCapProfile,
    ``warpedMetric,
    ``warpedMetric_metricInner_prod,
    ``warpedConnection_isLeviCivita,
    ``RoundCapProfile.puncturedMetric_tip,
    ``RoundCapProfile.puncturedMetric_tail,
    ``RoundCapProfile.radial_unit,
    ``RoundCapProfile.horizontal_radial,
    ``exists_round_tip_cylindrical_punctured_metric]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    unless (axioms.filter (fun a ↦ !allowed.contains a)).isEmpty do
      throwError "Nonstandard axioms for {name}: {axioms}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"CAP_WARPED_METRIC_GUARD_PASS {targets.size}"
