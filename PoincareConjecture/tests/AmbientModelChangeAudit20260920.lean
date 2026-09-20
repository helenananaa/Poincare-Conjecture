import PoincareConjecture.Topology.FiberSaturation.AmbientModelChange
import PoincareConjecture
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``PoincareConjecture.Topology.FiberSaturation.AmbientModelChange.modelChartedSpace,
    ``PoincareConjecture.Topology.FiberSaturation.AmbientModelChange.standard_manifold_of_boundaryless_model,
    ``PoincareConjecture.Topology.FiberSaturation.AmbientModelChange.extChartAt_recharted_eq,
    ``PoincareConjecture.Topology.FiberSaturation.AmbientModelChange.changeModel]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    unless (axioms.filter (fun a ↦ !allowed.contains a)).isEmpty do
      throwError "Unexpected axioms for {name}: {axioms}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"AMBIENT_MODEL_CHANGE_GUARD_PASS {names.size}"

#check PoincareConjecture.Topology.FiberSaturation.AmbientModelChange.changeModel
