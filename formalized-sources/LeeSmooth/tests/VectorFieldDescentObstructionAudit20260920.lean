import LeeSmoothLib.Verified.Counterexamples.VectorFieldDescent
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``VectorFieldDescentObstruction.coefficient_eq_abs_of_halfLine_rules,
    ``VectorFieldDescentObstruction.no_differentiable_descent_of_halfLine_rules]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing target: {name}"
    let axioms ← Lean.collectAxioms name
    unless (axioms.filter (fun a ↦ !allowed.contains a)).isEmpty do
      throwError "Unexpected axioms: {name}: {axioms}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"DESCENT_OBSTRUCTION_GUARD_PASS {names.size}"
