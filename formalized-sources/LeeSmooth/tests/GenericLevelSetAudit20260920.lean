import LeeSmoothLib.Verified.LevelSets.Generic
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``LeeVerifiedLevelSets.EmbeddingTransport.image_has_smooth_embedded_structure,
    ``LeeVerifiedLevelSets.Generic.regular_level_set_smooth_structure,
    ``LeeVerifiedLevelSets.Generic.constant_rank_level_set_smooth_structure_of_le,
    ``LeeVerifiedLevelSets.Generic.constant_rank_level_set_smooth_structure]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms: {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"GENERIC_LEVEL_SETS_GUARD_PASS {names.size}"
