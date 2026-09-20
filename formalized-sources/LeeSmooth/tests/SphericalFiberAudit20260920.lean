import LeeSmoothLib.Ch06.Sec06_45.Problem_6_9
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[``problem_6_9_transverse_to_sphere_iff,
    ``problem_6_9_preimage_is_embedded_submanifold,
    ``problem_6_9_scalarRegularLevel_isEmbeddedCurve,
    ``transportEmbeddedSubmanifoldR1ToReal,
    ``positiveSphere_isEmbeddedSubmanifold,
    ``problem_6_9_transverse_to_sphere_iff_regularValue]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in targets do
    unless (← getEnv).contains n do throwError "Missing declaration: {n}"
    let axs ← Lean.collectAxioms n
    let bad := axs.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms for {n}: {bad}"
    logInfo m!"PASS {n}: {axs}"
  logInfo m!"SPHERICAL_FIBER_GUARD_PASS {targets.size}"
