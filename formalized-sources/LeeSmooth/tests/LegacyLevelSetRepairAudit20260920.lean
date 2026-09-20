import LeeSmoothLib.Ch05.Sec05_30.Theorem_5_12
import LeeSmoothLib.Ch05.Sec05_30.Corollary_5_14
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[``constant_rank_level_set_has_embedded_submanifold_structure,
    ``regular_level_set_has_embedded_submanifold_structure,
    ``constant_rank_level_set_isProperlyEmbedded, ``regular_level_set_isProperlyEmbedded]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms: {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"LEGACY_LEVEL_SET_REPAIR_GUARD_PASS {names.size}"
