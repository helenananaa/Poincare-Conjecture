import LeeSmoothLib.Ch04.Sec04_21.HalfSpaceImmersionCriterion
import Lean

open Lean Elab Command in
run_cmd do
  let targets : Array Name := #[
    ``Manifold.isImmersionAt_of_injective_mfderiv_halfSpace,
    ``Manifold.isImmersion_of_injective_mfderiv_halfSpace,
    ``Manifold.isImmersion_of_injective_mfderiv_zero_selfModel]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in targets do
    unless (← getEnv).contains name do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    unless (axioms.filter (fun a ↦ !allowed.contains a)).isEmpty do
      throwError "Unexpected axioms for {name}: {axioms}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"HALFSPACE_IMMERSION_GUARD_PASS {targets.size}"

#check Manifold.isImmersion_of_injective_mfderiv_halfSpace
