import LeeSmoothLib.Verified.LevelSets.ModelTransport
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``LeeVerifiedLevelSets.ModelTransport.chartedSpaceCongr_isManifold,
    ``LeeVerifiedLevelSets.ModelTransport.euclideanChartedSpace_isManifold,
    ``LeeVerifiedLevelSets.ModelTransport.euclideanRechart_isManifold,
    ``LeeVerifiedLevelSets.ModelTransport.contMDiff_euclideanRechart_mk,
    ``LeeVerifiedLevelSets.ModelTransport.contMDiff_euclideanRechart_val,
    ``LeeVerifiedLevelSets.ModelTransport.euclideanRechartDiffeomorph,
    ``LeeVerifiedLevelSets.ModelTransport.contMDiff_rechartMap,
    ``LeeVerifiedLevelSets.ModelTransport.hasConstantRank_rechartMap,
    ``LeeVerifiedLevelSets.ModelTransport.isRegularValue_rechartMap]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms: {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"EUCLIDEAN_MODEL_TRANSPORT_GUARD_PASS {names.size}"
