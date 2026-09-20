import LeeSmoothLib.Ch08.Sec08_63.Problem_8_18
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``existsUnique_smooth_lift_of_eq_dim_submersion,
    ``smoothVectorFieldOfDescendedTangentMap,
    ``liftable_iff_pushforward_constant_on_fibers,
    ``existsUnique_smooth_base_vector_field_of_pushforward_constant_on_fibers]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in targets do
    unless (← getEnv).contains target do throwError "Missing declaration: {target}"
    let axioms ← Lean.collectAxioms target
    unless (axioms.filter (fun a ↦ !allowed.contains a)).isEmpty do
      throwError "Unaccepted axioms: {target}: {axioms}"
    logInfo m!"PASS {target}: {axioms}"
  logInfo m!"VECTOR_DESCENT_GUARD_PASS {targets.size}"

#check liftable_iff_pushforward_constant_on_fibers
#check existsUnique_smooth_base_vector_field_of_pushforward_constant_on_fibers
