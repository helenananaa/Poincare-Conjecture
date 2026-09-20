import LeeSmoothLib.Verified.LevelSets.DiffeomorphTransport
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``LeeVerifiedLevelSets.DiffeomorphTransport.mfderiv_comp_diffeomorphs,
    ``LeeVerifiedLevelSets.DiffeomorphTransport.surjective_mfderiv_comp_diffeomorphs_iff,
    ``LeeVerifiedLevelSets.DiffeomorphTransport.rankAt_comp_diffeomorphs,
    ``LeeVerifiedLevelSets.DiffeomorphTransport.isRegularValue_comp_diffeomorphs_iff,
    ``LeeVerifiedLevelSets.DiffeomorphTransport.hasConstantRank_comp_diffeomorphs_iff]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms in {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"DIFFEOMORPH_TRANSPORT_GUARD_PASS {names.size}"
