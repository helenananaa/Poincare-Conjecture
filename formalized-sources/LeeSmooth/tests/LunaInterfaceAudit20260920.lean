import LeeSmoothLib.Ch07.Sec07_48.Theorem_7_7
import LeeSmoothLib.Ch04.Sec04_27.Problem_4_12
import LeeSmoothLib.Ch06.Sec06_45.Problem_6_9
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``exists_universal_covering_group,
    ``torus_of_revolution_map_isImmersion,
    ``torus_of_revolution_map_isSmoothEmbedding,
    ``range_torus_of_revolution_map,
    ``positiveSphere_isEmbeddedSubmanifold,
    ``transportEmbeddedSubmanifoldR1ToReal,
    ``problem_6_9_scalarRegularLevel_isEmbeddedCurve]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing target {name}"
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter (fun a ↦ !allowed.contains a)
    unless unexpected.isEmpty do throwError "Unexpected axioms for {name}: {unexpected}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"LUNA_INTERFACE_GUARD_PASS {targets.size}"
