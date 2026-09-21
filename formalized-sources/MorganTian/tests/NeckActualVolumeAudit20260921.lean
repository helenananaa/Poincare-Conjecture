import MorganTianLib.Ch02.NeckVolume.ActualVolumeComparison
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``MorganTianLib.riemannianMeasure_image_of_pullback_metric,
    ``MorganTianLib.epsilonNeck_volume_rescaling,
    ``MorganTianLib.epsilonNeck_volume_comparison]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing theorem: {name}"
    let axioms ← Lean.collectAxioms name
    unless (axioms.filter (fun a ↦ !allowed.contains a)).isEmpty do
      throwError "Unexpected axioms: {name}: {axioms}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"ACTUAL_NECK_VOLUME_GUARD_PASS {names.size}"

#check MorganTianLib.riemannianMeasure_image_of_pullback_metric
#check MorganTianLib.epsilonNeck_volume_rescaling
#check MorganTianLib.epsilonNeck_volume_comparison
