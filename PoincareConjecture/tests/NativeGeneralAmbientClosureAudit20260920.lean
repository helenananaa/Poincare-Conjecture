import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.GeneralAmbientCutClosure
import PoincareConjecture
import Lean

open Lean Elab Command in
run_cmd do
  let name := ``PoincareConjecture.Topology.FiberSaturation.SmoothNeck.exists_smoothClosure_of_native_neck_cut_cover_of_finite_dimensional_model
  unless (← getEnv).contains name do throwError "Missing declaration: {name}"
  let axioms ← Lean.collectAxioms name
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let bad := axioms.filter (fun a ↦ !allowed.contains a)
  unless bad.isEmpty do throwError "Unexpected axioms for {name}: {bad}"
  logInfo m!"PASS {name}: {axioms}"
  logInfo "NATIVE_GENERAL_AMBIENT_CLOSURE_GUARD_PASS 1"

#check PoincareConjecture.Topology.FiberSaturation.SmoothNeck.exists_smoothClosure_of_native_neck_cut_cover_of_finite_dimensional_model
