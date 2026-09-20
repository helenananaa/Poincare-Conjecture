import LeeSmoothLib.Ch06.Sec06_39.SardBoundaryManifolds
import LeeSmoothLib.Ch08.Sec08_58.Proposition_8_23
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``SardBoundaryManifolds.criticalValues_has_measure_zero_in_manifold_of_contMDiff_halfSpace,
    ``VectorField.existsUnique_restriction_to_submanifold]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter (fun n ↦ !allowed.contains n)
    unless unexpected.isEmpty do throwError "Nonstandard axioms: {name}: {unexpected}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"CONTINUATION_2042_GUARD_PASS {names.size}"
