import LeeSmoothLib.Ch06.Sec06_45.Problem_6_11
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``compRangeSup_eq_top_iff_rangeSupComap_eq_top,
    ``preimageTangentSpaceEqComap_atCompositePoint,
    ``compositeTransversePointwise_iff_preimageTransversePointwise,
    ``transverse_preimage_iff_comp_transverse]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Unaccepted axioms for {name}: {bad}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"TRANSVERSE_COMPOSITION_GUARD_PASS {targets.size}"
