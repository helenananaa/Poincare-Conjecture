import MorganTianLib.Ch02.NeckVolume.CompactCapGap
import MorganTianLib.Ch02.NeckVolume.RoundCoordinates
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``MorganTianLib.roundCylinder_extChartAt_apply,
    ``MorganTianLib.roundCylinder_extChartAt_symm_axis,
    ``MorganTianLib.haar_cylinder_box_volume_lower,
    ``MorganTianLib.roundCylinderCoordinateDensity_continuous_pos,
    ``MorganTianLib.roundCylinder_chartVolumeDensity_eq_coordinateDensity,
    ``MorganTianLib.roundCylinder_fractional_region_volume_lower,
    ``MorganTianLib.epsilonNeck_volume_dominates_fixed_compact_cap]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let rejected := axioms.filter (fun a ↦ !allowed.contains a)
    unless rejected.isEmpty do throwError "Unaccepted axioms for {name}: {rejected}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"ROUND_VOLUME_LOWER_GUARD_PASS {targets.size}"

#check MorganTianLib.roundCylinder_fractional_region_volume_lower
#check MorganTianLib.epsilonNeck_volume_dominates_fixed_compact_cap
